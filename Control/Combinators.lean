/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Init
/-!
# Monad combinators, as in Haskell's Control.Monad.
-/

@[expose] public section

universe u v w

/-- Collapses two layers of monadic structure into one,
passing the effects of the inner monad through the outer. -/
/-
**joinM** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：joinM {m : Type u -> Type u} [Monad m] {α : Type u} (a : m (m α)) : m α
参数：a : m (m α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Collapses two layers of monadic structure into one,
passing the effects of the inner monad through the outer.
-/
def joinM {m : Type u → Type u} [Monad m] {α : Type u} (a : m (m α)) : m α :=
  bind a id

/-- Executes `tm` or `fm` depending on whether the result of `mbool` is `true` or `false`
respectively. -/
/-
**condM** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：condM {m : Type -> Type} [Monad m] {α : Type} (mbool : m Bool) (tm fm : m 
α) : m α
参数：mbool : m Bool；tm fm : m α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Executes `tm` or `fm` depending on whether the result of `mbool` is `true` or `f
alse`
respectively.
-/
def condM {m : Type → Type} [Monad m] {α : Type} (mbool : m Bool) (tm fm : m α) : m α := do
  let b ← mbool
  cond b tm fm
