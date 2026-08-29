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

/--
Definition of `joinM` / `joinM` 的定义

English:
definition joinM
  signature: {m : Type u -> Type u} [Monad m] {α : Type u} (a : m (m α))
  body: bind a id

中文:
定义 joinM
  签名: {m : 类型u -> 类型u} [单子 m] {α : 类型u} (a : m (m α))
  定义体: bind a id
-/
def joinM {m : Type u -> Type u} [Monad m] {α : Type u} (a : m (m α)) : m α :=
  bind a id

/--
Definition of `condM` / `condM` 的定义

English:
definition condM
  signature: {m : Type -> Type} [Monad m] {α : Type} (mbool : m Bool) (tm fm : m α)
  body: do
  let b ← mbool
  cond b tm fm

中文:
定义 condM
  签名: {m : 类型 -> 类型} [单子 m] {α : 类型} (mbool : m 布尔值) (tm fm : m α)
  定义体: do
  let b ← mbool
  cond b tm fm
-/
def condM {m : Type -> Type} [Monad m] {α : Type} (mbool : m Bool) (tm fm : m α) : m α := do
  let b ← mbool
  cond b tm fm
