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
/-
**map_eq_bind_pure_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_eq_bind_pure_comp (m : Type u -> Type v) [Monad m] [LawfulMonad m] (f 
: α -> β) (x : m α) : f < > x = x >>= pure ∘ f
参数：m : Type u -> Type v；f : α -> β；x : m α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LawfulMonad.bind_pure_comp`：∀ {m : Type u → Type v} {inst : Monad m} [se
lf : LawfulMonad m] {α β : Type u} (f : α → β) (x : m α),   (do       let a ← x 
      pure (f a)…
-/
theorem map_eq_bind_pure_comp (m : Type u → Type v) [Monad m] [LawfulMonad m]
    (f : α → β) (x : m α) : f <$> x = x >>= pure ∘ f :=
  (bind_pure_comp f x).symm

/-- run a `StateT` program and discard the final state -/
/-
**StateT.eval** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StateT.eval {m : Type u -> Type v} [Functor m] (cmd : StateT σ m α) (s : σ
) : m α
参数：cmd : StateT σ m α；s : σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
run a `StateT` program and discard the final state
-/
def StateT.eval {m : Type u → Type v} [Functor m] (cmd : StateT σ m α) (s : σ) : m α :=
  Prod.fst <$> cmd.run s

universe u₀ u₁ v₀ v₁
/-- reduce the equivalence between two state monads to the equivalence between
their respective function spaces -/
/-
**StateT.equiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StateT.equiv {σ₁ α₁ : Type u₀} {σ₂ α₂ : Type u₁} {m₁ : Type u₀ -> Type v₀}
 {m₂ : Type u₁ -> Type v₁} (F : (σ₁ -> m₁ (α₁ × σ₁)) ≃ (σ₂ -> m₂ (α₂ × σ₂))) : S
tateT σ₁ m₁ α₁ ≃ StateT σ₂ m₂ α₂
参数：F : (σ₁ -> m₁ (α₁ × σ₁)) ≃ (σ₂ -> m₂ (α₂ × σ₂))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
reduce the equivalence between two state monads to the equivalence between
their respective function spaces
-/
def StateT.equiv {σ₁ α₁ : Type u₀} {σ₂ α₂ : Type u₁}
    {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁}
    (F : (σ₁ → m₁ (α₁ × σ₁)) ≃ (σ₂ → m₂ (α₂ × σ₂))) : StateT σ₁ m₁ α₁ ≃ StateT σ₂ m₂ α₂ :=
  F

/-- reduce the equivalence between two reader monads to the equivalence between
their respective function spaces -/
/-
**ReaderT.equiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ReaderT.equiv {ρ₁ α₁ : Type u₀} {ρ₂ α₂ : Type u₁} {m₁ : Type u₀ -> Type v₀
} {m₂ : Type u₁ -> Type v₁} (F : (ρ₁ -> m₁ α₁) ≃ (ρ₂ -> m₂ α₂)) : ReaderT ρ₁ m₁ 
α₁ ≃ ReaderT ρ₂ m₂ α₂
参数：F : (ρ₁ -> m₁ α₁) ≃ (ρ₂ -> m₂ α₂)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
reduce the equivalence between two reader monads to the equivalence between
their respective function spaces
-/
def ReaderT.equiv {ρ₁ α₁ : Type u₀} {ρ₂ α₂ : Type u₁}
    {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁}
    (F : (ρ₁ → m₁ α₁) ≃ (ρ₂ → m₂ α₂)) : ReaderT ρ₁ m₁ α₁ ≃ ReaderT ρ₂ m₂ α₂ :=
  F
