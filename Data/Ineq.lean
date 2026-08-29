/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public import Mathlib.Lean.Expr.Basic

/-!
# `Ineq` datatype

This file contains an enum `Ineq` (whose constructors are `eq`, `le`, `lt`), and operations
involving it. The type `Ineq` is one of the fundamental objects manipulated by the `linarith` and
`linear_combination` tactics.
-/

@[expose] public section

open Lean Meta

namespace Mathlib

/-! ### Inequalities -/

/--
Inductive type `Ineq` / 归纳类型 `Ineq`

English:
inductive Ineq
  parameters: : Type
  constructors (1):
    - eq: | le | lt

中文:
归纳类型 Ineq
  参数: : 类型
  构造子 (1 个):
    - eq: | le | lt
-/
inductive Ineq : Type
  | eq | le | lt
deriving DecidableEq, Inhabited, Repr

namespace Ineq

/--
Definition of `max` / `max` 的定义

English:
definition max
  signature: : Ineq -> Ineq -> Ineq

中文:
定义 最大值
  签名: : Ineq -> Ineq -> Ineq
-/
def max : Ineq -> Ineq -> Ineq
  | lt, _ => lt
  | _, lt => lt
  | le, _ => le
  | _, le => le
  | eq, eq => eq

/--
Definition of `cmp` / `cmp` 的定义

English:
definition cmp
  signature: : Ineq -> Ineq -> Ordering

中文:
定义 cmp
  签名: : Ineq -> Ineq -> Ordering
-/
def cmp : Ineq -> Ineq -> Ordering
  | eq, eq => Ordering.eq
  | eq, _ => Ordering.lt
  | le, le => Ordering.eq
  | le, lt => Ordering.lt
  | lt, lt => Ordering.eq
  | _, _ => Ordering.gt

/--
Definition of `toString` / `toString` 的定义

English:
definition toString
  signature: : Ineq -> String

中文:
定义 toString
  签名: : Ineq -> String
-/
def toString : Ineq -> String
  | eq => "="
  | le => "<="
  | lt => "<"

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToString Ineq
  body: ⟨toString⟩

中文:
实例 :
  签名: ToString Ineq
  定义体: ⟨toString⟩

Depends on / 依赖: toString
-/
instance : ToString Ineq := ⟨toString⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToFormat Ineq
  body: ⟨fun i => Ineq.toString i⟩

中文:
实例 :
  签名: ToFormat Ineq
  定义体: ⟨fun i => Ineq.toString i⟩

Depends on / 依赖: Ineq.toString, toString
-/
instance : ToFormat Ineq := ⟨fun i => Ineq.toString i⟩

end Mathlib.Ineq

/-! ### Parsing inequalities -/

namespace Lean.Expr
open Mathlib

/--
Definition of `ineq?` / `ineq?` 的定义

English:
definition ineq?
  signature: (e : Expr)
  body: do
  let e ← whnfR (← instantiateMVars e)
  match e.eq? with
  | some p => return (Ineq.eq, p)
  | none =>
  match e.le? with
  | some p => return (Ineq.le, p)
  | none =>
  match e.lt? with
  | some p => return (Ineq.lt, p)
  | none => throwError "Not a comparison: {e}"

中文:
定义 ineq?
  签名: (e : Expr)
  定义体: do
  let e ← whnfR (← instantiateMVars e)
  match e.eq? with
  | some p => return (Ineq.eq, p)
  | none =>
  match e.le? with
  | some p => return (Ineq.le, p)
  | none =>
  match e.lt? with
  | some p => return (Ineq.lt, p)
  | none => throwError "Not a comparison: {e}"
-/
def ineq? (e : Expr) : MetaM (Ineq × Expr × Expr × Expr) := do
  let e ← whnfR (← instantiateMVars e)
  match e.eq? with
  | some p => return (Ineq.eq, p)
  | none =>
  match e.le? with
  | some p => return (Ineq.le, p)
  | none =>
  match e.lt? with
  | some p => return (Ineq.lt, p)
  | none => throwError "Not a comparison: {e}"

/--
Definition of `ineqOrNotIneq?` / `ineqOrNotIneq?` 的定义

English:
definition ineqOrNotIneq?
  signature: (e : Expr)
  body: do
  try
    return (true, ← e.ineq?)
  catch _ =>
    let some e' := e.not? | throwError "Not a comparison: {e}"
    return (false, ← e'.ineq?)

中文:
定义 ineqOrNotIneq?
  签名: (e : Expr)
  定义体: do
  try
    return (true, ← e.ineq?)
  catch _ =>
    let some e' := e.not? | throwError "Not a comparison: {e}"
    return (false, ← e'.ineq?)
-/
def ineqOrNotIneq? (e : Expr) : MetaM (Bool × Ineq × Expr × Expr × Expr) := do
  try
    return (true, ← e.ineq?)
  catch _ =>
    let some e' := e.not? | throwError "Not a comparison: {e}"
    return (false, ← e'.ineq?)

end Lean.Expr
