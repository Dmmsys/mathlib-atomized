/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Patrick Massot, Kyle Miller
-/
module

public import Mathlib.Init
public import Lean.Meta.Tactic.Rewrite

/-!
# Additional declarations for `Lean.Meta.Tactic.Rewrite`
-/

@[expose] public section

namespace Lean.Expr

open Meta

/--
Rewrites `e` via some `eq`, producing a proof `e = e'` for some `e'`.

Rewrites with a fresh metavariable as the ambient goal.
Fails if the rewrite produces any subgoals.
-/
/-
**Lean.Expr.rewrite** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Expr`。
形式化陈述：rewrite (e eq : Expr) : MetaM Expr
参数：e eq : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Rewrites `e` via some `eq`, producing a proof `e = e'` for some `e'`.

Rewrites with a fresh metavariable as the ambient goal.
Fails if the rewrite produces any subgoals.
-/
def rewrite (e eq : Expr) : MetaM Expr := do
  let ⟨_, eq', []⟩ ← (← mkFreshExprMVar none).mvarId!.rewrite e eq
    | throwError "Expr.rewrite may not produce subgoals."
  return eq'

/--
Rewrites the type of `e` via some `eq`, then moves `e` into the new type via `Eq.mp`.

Rewrites with a fresh metavariable as the ambient goal.
Fails if the rewrite produces any subgoals.
-/
/-
**Lean.Expr.rewriteType** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Expr`。
形式化陈述：rewriteType (e eq : Expr) : MetaM Expr
参数：e eq : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Rewrites the type of `e` via some `eq`, then moves `e` into the new type via `Eq
.mp`.

Rewrites with a fresh metavariable as the ambient goal.
Fails if the rewrite produces any subgoals.
-/
def rewriteType (e eq : Expr) : MetaM Expr := do
  mkEqMP (← (← inferType e).rewrite eq) e

end Lean.Expr

