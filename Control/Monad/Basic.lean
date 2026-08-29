/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Batteries.Lean.Except

import Mathlib.Tactic.Attr.Register

/-!
# Monad

## Attributes

* `ext`
* `functor_norm`
* `monad_norm`

## Implementation Details

Set of rewrite rules and automation for monads in general and
`ReaderT`, `StateT`, `ExceptT` and `OptionT` in particular.

The rewrite rules for monads are carefully chosen so that `simp with functor_norm`
will not introduce monadic vocabulary in a context where
applicatives would do just fine but will handle monadic notation
already present in an expression.

In a context where monadic reasoning is desired `simp with monad_norm`
will translate functor and applicative notation into monad notation
and use regular `functor_norm` rules as well.

## Tags

functor, applicative, monad, simp

-/

@[expose] public section

universe u v
variable {α β σ : Type u}

attribute [ext] ReaderT.ext StateT.ext ExceptT.ext

@[monad_norm]
/--
theorem `map_eq_bind_pure_comp` / 定理 `map_eq_bind_pure_comp`

English:
theorem map_eq_bind_pure_comp
  statement: (m : Type u -> Type v) [Monad m] [LawfulMonad m]
  proof: (bind_pure_comp f x).symm

中文:
定理 map_eq_bind_pure_comp
  结论: (m : 类型u -> 类型v) [单子 m] [合法单子 m]
  证明: (bind_pure_comp f x).symm

Depends on / 依赖: bind_pure_comp
-/
theorem map_eq_bind_pure_comp (m : Type u -> Type v) [Monad m] [LawfulMonad m]
(f : α -> β) (x : m α) : f < > x = x >>= pure ∘ f :=
  (bind_pure_comp f x).symm

/--
Definition of `StateT.eval` / `StateT.eval` 的定义

English:
definition StateT.eval
  signature: {m : Type u -> Type v} [Functor m] (cmd : StateT σ m α) (s : σ)
  body: Prod.fst < > cmd.run s

universe u₀ u₁ v₀ v₁

中文:
定义 StateT.eval
  签名: {m : 类型u -> 类型v} [函子 m] (cmd : StateT σ m α) (s : σ)
  定义体: Prod.fst < > cmd.run s

universe u₀ u₁ v₀ v₁

Depends on / 依赖: Prod.fst, cmd.run
-/
def StateT.eval {m : Type u -> Type v} [Functor m] (cmd : StateT σ m α) (s : σ) : m α :=
Prod.fst < > cmd.run s

universe u₀ u₁ v₀ v₁
/--
Definition of `StateT.equiv` / `StateT.equiv` 的定义

English:
definition StateT.equiv
  signature: {σ₁ α₁ : Type u₀} {σ₂ α₂ : Type u₁}
  body: F

中文:
定义 StateT.equiv
  签名: {σ₁ α₁ : 类型u₀} {σ₂ α₂ : 类型u₁}
  定义体: F
-/
def StateT.equiv {σ₁ α₁ : Type u₀} {σ₂ α₂ : Type u₁}
    {m₁ : Type u₀ -> Type v₀} {m₂ : Type u₁ -> Type v₁}
    (F : (σ₁ -> m₁ (α₁ × σ₁)) ≃ (σ₂ -> m₂ (α₂ × σ₂))) : StateT σ₁ m₁ α₁ ≃ StateT σ₂ m₂ α₂ :=
  F

/--
Definition of `ReaderT.equiv` / `ReaderT.equiv` 的定义

English:
definition ReaderT.equiv
  signature: {ρ₁ α₁ : Type u₀} {ρ₂ α₂ : Type u₁}
  body: F

中文:
定义 ReaderT.equiv
  签名: {ρ₁ α₁ : 类型u₀} {ρ₂ α₂ : 类型u₁}
  定义体: F
-/
def ReaderT.equiv {ρ₁ α₁ : Type u₀} {ρ₂ α₂ : Type u₁}
    {m₁ : Type u₀ -> Type v₀} {m₂ : Type u₁ -> Type v₁}
    (F : (ρ₁ -> m₁ α₁) ≃ (ρ₂ -> m₂ α₂)) : ReaderT ρ₁ m₁ α₁ ≃ ReaderT ρ₂ m₂ α₂ :=
  F
