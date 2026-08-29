/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Init
public import Qq
public import Qq.Typ

/-! # Helpers to invoke functions involving algebra at tactic time

This file provides instances on `x y : Q($α)` such that `x + y = q($x + $y)`.
-/

@[expose] public section
open Qq

/-- Produce a `One` instance for `Q($α)` such that `1 : Q($α)` is `q(1 : $α)`. -/
@[instance_reducible]
/--
Definition of `Expr.instOne` / `Expr.instOne` 的定义

English:
definition Expr.instOne
  signature: {u : Lean.Level} (α : Q(Type u)) (_ : Q(One $α))
  body: q(1 : $α)

中文:
定义 Expr.instOne
  签名: {u : Lean.Level} (α : Q(类型u)) (_ : Q(幺 $α))
  定义体: q(1 : $α)
-/
def Expr.instOne {u : Lean.Level} (α : Q(Type u)) (_ : Q(One $α)) : One Q($α) where
  one := q(1 : $α)

/-- Produce a `Zero` instance for `Q($α)` such that `0 : Q($α)` is `q(0 : $α)`. -/
@[instance_reducible]
/--
Definition of `Expr.instZero` / `Expr.instZero` 的定义

English:
definition Expr.instZero
  signature: {u : Lean.Level} (α : Q(Type u)) (_ : Q(Zero $α))
  body: q(0 : $α)

中文:
定义 Expr.instZero
  签名: {u : Lean.Level} (α : Q(类型u)) (_ : Q(零 $α))
  定义体: q(0 : $α)
-/
def Expr.instZero {u : Lean.Level} (α : Q(Type u)) (_ : Q(Zero $α)) : Zero Q($α) where
  zero := q(0 : $α)

/-- Produce a `Mul` instance for `Q($α)` such that `x * y : Q($α)` is `q($x * $y)`. -/
@[instance_reducible]
/--
Definition of `Expr.instMul` / `Expr.instMul` 的定义

English:
definition Expr.instMul
  signature: {u : Lean.Level} (α : Q(Type u)) (_ : Q(Mul $α))
  body: q($x * $y)

中文:
定义 Expr.instMul
  签名: {u : Lean.Level} (α : Q(类型u)) (_ : Q(乘法 $α))
  定义体: q($x * $y)
-/
def Expr.instMul {u : Lean.Level} (α : Q(Type u)) (_ : Q(Mul $α)) : Mul Q($α) where
  mul x y := q($x * $y)

/-- Produce an `Add` instance for `Q($α)` such that `x + y : Q($α)` is `q($x + $y)`. -/
@[instance_reducible]
/--
Definition of `Expr.instAdd` / `Expr.instAdd` 的定义

English:
definition Expr.instAdd
  signature: {u : Lean.Level} (α : Q(Type u)) (_ : Q(Add $α))
  body: q($x + $y)

中文:
定义 Expr.instAdd
  签名: {u : Lean.Level} (α : Q(类型u)) (_ : Q(加法 $α))
  定义体: q($x + $y)
-/
def Expr.instAdd {u : Lean.Level} (α : Q(Type u)) (_ : Q(Add $α)) : Add Q($α) where
  add x y := q($x + $y)
