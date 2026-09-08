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
/-
**Expr.instOne** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Expr.instOne {u : Lean.Level} (α : Q(Type u)) (_ : Q(One $α)) : One Q($α) 
where one
参数：α : Q(Type u)；_ : Q(One $α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Produce a `One` instance for `Q($α)` such that `1 : Q($α)` is `q(1 : $α)`.
-/
def Expr.instOne {u : Lean.Level} (α : Q(Type u)) (_ : Q(One $α)) : One Q($α) where
  one := q(1 : $α)

/-- Produce a `Zero` instance for `Q($α)` such that `0 : Q($α)` is `q(0 : $α)`. -/
@[instance_reducible]
/-
**Expr.instZero** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Expr.instZero {u : Lean.Level} (α : Q(Type u)) (_ : Q(Zero $α)) : Zero Q($
α) where zero
参数：α : Q(Type u)；_ : Q(Zero $α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Produce a `Zero` instance for `Q($α)` such that `0 : Q($α)` is `q(0 : $α)`.
-/
def Expr.instZero {u : Lean.Level} (α : Q(Type u)) (_ : Q(Zero $α)) : Zero Q($α) where
  zero := q(0 : $α)

/-- Produce a `Mul` instance for `Q($α)` such that `x * y : Q($α)` is `q($x * $y)`. -/
@[instance_reducible]
/-
**Expr.instMul** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Expr.instMul {u : Lean.Level} (α : Q(Type u)) (_ : Q(Mul $α)) : Mul Q($α) 
where mul x y
参数：α : Q(Type u)；_ : Q(Mul $α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Produce a `Mul` instance for `Q($α)` such that `x * y : Q($α)` is `q($x * $y)`.
-/
def Expr.instMul {u : Lean.Level} (α : Q(Type u)) (_ : Q(Mul $α)) : Mul Q($α) where
  mul x y := q($x * $y)

/-- Produce an `Add` instance for `Q($α)` such that `x + y : Q($α)` is `q($x + $y)`. -/
@[instance_reducible]
/-
**Expr.instAdd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Expr.instAdd {u : Lean.Level} (α : Q(Type u)) (_ : Q(Add $α)) : Add Q($α) 
where add x y
参数：α : Q(Type u)；_ : Q(Add $α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Produce an `Add` instance for `Q($α)` such that `x + y : Q($α)` is `q($x + $y)`.
-/
def Expr.instAdd {u : Lean.Level} (α : Q(Type u)) (_ : Q(Add $α)) : Add Q($α) where
  add x y := q($x + $y)
