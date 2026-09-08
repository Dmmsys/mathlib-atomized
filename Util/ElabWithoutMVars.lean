/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Init

/-!
# `elabTermWithoutNewMVars`

-/

public meta section

open Lean Elab Tactic

/-- Elaborates a term with `errToSorry = false` and ensuring it has no metavariables. -/
/-
**elabTermWithoutNewMVars** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：elabTermWithoutNewMVars (tactic : Name) (t : Term) : TacticM Expr
参数：tactic : Name；t : Term。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Elaborates a term with `errToSorry = false` and ensuring it has no metavariables
.
-/
def elabTermWithoutNewMVars (tactic : Name) (t : Term) : TacticM Expr := Term.withoutErrToSorry do
  let (e, mvars) ← elabTermWithHoles t none tactic
  unless mvars.isEmpty do
    throwErrorAt t "Argument passed to {tactic} has metavariables:{indentD e}"
  return e
