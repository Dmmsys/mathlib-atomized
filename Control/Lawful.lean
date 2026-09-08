/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

public import Mathlib.Init

/-!
# Functor Laws, applicative laws, and monad Laws
-/

public section

universe u v

namespace StateT

section

variable {σ : Type u} {m : Type u → Type v} {α β : Type u}

/-- A copy of `LawfulFunctor.map_const` for `StateT` that holds even if `m` is not lawful. -/
/-
**StateT.map_const** 是 Mathlib 中的一个定理，位于命名空间 `StateT`。
形式化陈述：∀ {σ : Type u} {m : Type u → Type v} {α β : Type u} [inst : Monad m], Func
tor.mapConst = Functor.map ∘ Function.const β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A copy of `LawfulFunctor.map_const` for `StateT` that holds even if `m` is not l
awful.
-/
protected lemma map_const [Monad m] :
    (Functor.mapConst : α → StateT σ m β → StateT σ m α) = Functor.map ∘ Function.const β :=
  rfl
/-
**StateT.run_mapConst** 是 Mathlib 中的一个定理，位于命名空间 `StateT`。
形式化陈述：∀ {σ : Type u} {m : Type u → Type v} {α β : Type u} [inst : Monad m] [Lawf
ulMonad m] (x : StateT σ m α) (y : β)   (st : σ), (Functor.mapConst y x).run st 
= Prod.map (Function.const α y) id <$> x.run st
参数：x : StateT σ m α；y : β；st : σ；Functor.mapConst y x；Function.const α y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StateT.run_map`：∀ {m : Type u → Type u_1} {α β σ : Type u} [inst : Monad
 m] [LawfulMonad m] (f : α → β) (x : StateT σ m α) (s : σ),   (f <$> x).run s = 
(fun…
-/
@[simp] lemma run_mapConst [Monad m] [LawfulMonad m] (x : StateT σ m α) (y : β) (st : σ) :
    (Functor.mapConst y x).run st = Prod.map (Function.const α y) id <$> x.run st := run_map _ _ _

end

end StateT

namespace ExceptT

variable {α ε : Type u} {m : Type u → Type v} (x : ExceptT ε m α)

attribute [simp] run_bind

@[simp]
/-
**ExceptT.run_monadLift** 是 Mathlib 中的一个定理，位于命名空间 `ExceptT`。
形式化陈述：run_monadLift {n} [Monad m] [MonadLiftT n m] (x : n α) : (monadLift x : Ex
ceptT ε m α).run = Except.ok < > (monadLift x : m α)
参数：x : n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem run_monadLift {n} [Monad m] [MonadLiftT n m] (x : n α) :
    (monadLift x : ExceptT ε m α).run = Except.ok <$> (monadLift x : m α) :=
  rfl

end ExceptT

