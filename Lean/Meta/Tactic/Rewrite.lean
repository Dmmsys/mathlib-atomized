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
Definition of `rewrite` / `rewrite` 的定义

English:
definition rewrite
  signature: (e eq : Expr)
  body: do
  let ⟨_, eq', []⟩ ← (← mkFreshExprMVar none).mvarId!.rewrite e eq
    | throwError "Expr.rewrite may not produce subgoals."
  return eq'

中文:
定义 rewrite
  签名: (e eq : Expr)
  定义体: do
  let ⟨_, eq', []⟩ ← (← mkFreshExprMVar none).mvarId!.rewrite e eq
    | throwError "Expr.rewrite may not produce subgoals."
  return eq'
-/
def rewrite (e eq : Expr) : MetaM Expr := do
  let ⟨_, eq', []⟩ ← (← mkFreshExprMVar none).mvarId!.rewrite e eq
    | throwError "Expr.rewrite may not produce subgoals."
  return eq'

/--
Definition of `rewriteType` / `rewriteType` 的定义

English:
definition rewriteType
  signature: (e eq : Expr)
  body: do
  mkEqMP (← (← inferType e).rewrite eq) e

中文:
定义 rewriteType
  签名: (e eq : Expr)
  定义体: do
  mkEqMP (← (← inferType e).rewrite eq) e
-/
def rewriteType (e eq : Expr) : MetaM Expr := do
  mkEqMP (← (← inferType e).rewrite eq) e

end Lean.Expr
