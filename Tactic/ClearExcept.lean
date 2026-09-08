/-
Copyright (c) 2022 Joshua Clune. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joshua Clune
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.ElabTerm

/-!
# The `clear*` tactic

This file provides a variant of the `clear` tactic, which clears all hypotheses it can
besides a provided list, class instances, and auxiliary declarations.
-/

public meta section

open Lean.Meta

namespace Lean.Elab.Tactic

/-- Returns the free variable IDs that can be cleared, excluding those in the preserve list,
/-
**Lean.Elab.Tactic.instances** 是 Mathlib 中的一个类，位于命名空间 `Lean.Elab.Tactic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class instances, and auxiliary declarations (e.g. recursive hypotheses). -/
/-
**Lean.Elab.Tactic.getVarsToClear** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Elab.Tactic`。
形式化陈述：getVarsToClear (preserve : Array FVarId) : MetaM (Array FVarId)
参数：preserve : Array FVarId。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Returns the free variable IDs that can be cleared, excluding those in the preser
ve list,
class instances, and auxiliary declarations (e.g. recursive hypotheses).
-/
def getVarsToClear (preserve : Array FVarId) : MetaM (Array FVarId) := do
  let mut toClear : Array FVarId := #[]
  for decl in ← getLCtx do
    unless preserve.contains decl.fvarId || decl.isAuxDecl do
      if let none ← isClass? decl.type then
        toClear := toClear.push decl.fvarId
  return toClear

/-- Clears all hypotheses from a goal except those in the preserve list, class instances, and
auxiliary declarations (e.g. recursive hypotheses). -/
/-
**Lean.Elab.Tactic.clearExcept** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Elab.Tactic`。
形式化陈述：clearExcept (preserve : Array FVarId) (goal : MVarId) : MetaM MVarId
参数：preserve : Array FVarId；goal : MVarId。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Clears all hypotheses from a goal except those in the preserve list, class insta
nces, and
auxiliary declarations (e.g. recursive hypotheses).
-/
def clearExcept (preserve : Array FVarId) (goal : MVarId) : MetaM MVarId := do
  let toClear ← getVarsToClear preserve
  goal.tryClearMany toClear

/-- Clears all hypotheses it can, except those provided after a minus sign, class instances, and
hidden auxiliary declarations (for example recursive hypotheses). Example:
```
  clear * - h₁ h₂
```
The intent is that `clear * -` only clears user-visible local declarations; hidden auxiliary
declarations should be handled by more specific mechanisms when needed. -/
syntax (name := clearExceptTactic) "clear " "*" " -" (ppSpace colGt ident)* : tactic

elab_rules : tactic
  | `(tactic| clear * - $hs:ident*) => do
    let fvarIds ← getFVarIds hs
    liftMetaTactic1 fun goal ↦ clearExcept fvarIds goal

end Lean.Elab.Tactic

