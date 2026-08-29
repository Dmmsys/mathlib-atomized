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

variable {σ : Type u} {m : Type u -> Type v} {α β : Type u}

/--
lemma `map_const` / 引理 `map_const`

English:
lemma map_const
  given: [Monad m]
  proof: rfl

中文:
引理 map_const
  条件: [单子 m]
  证明: rfl
-/
protected lemma map_const [Monad m] :
    (Functor.mapConst : α -> StateT σ m β -> StateT σ m α) = Functor.map ∘ Function.const β :=
  rfl

/--
lemma `run_mapConst` / 引理 `run_mapConst`

English:
lemma run_mapConst
  given: [Monad m] [LawfulMonad m] (x : StateT σ m α) (y : β) (st : σ)
  proof: run_map _ _ _

中文:
引理 run_mapConst
  条件: [单子 m] [合法单子 m] (x : StateT σ m α) (y : β) (st : σ)
  证明: run_map _ _ _
-/
@[simp] lemma run_mapConst [Monad m] [LawfulMonad m] (x : StateT σ m α) (y : β) (st : σ) :
(Functor.mapConst y x).run st = Prod.map (Function.const α y) id < > x.run st := run_map _ _ _

end

end StateT

namespace ExceptT

variable {α ε : Type u} {m : Type u -> Type v} (x : ExceptT ε m α)

attribute [simp] run_bind

@[simp]
/--
theorem `run_monadLift` / 定理 `run_monadLift`

English:
theorem run_monadLift
  given: {n} [Monad m] [MonadLiftT n m] (x : n α)
  proof: rfl

中文:
定理 run_monadLift
  条件: {n} [单子 m] [MonadLiftT n m] (x : n α)
  证明: rfl
-/
theorem run_monadLift {n} [Monad m] [MonadLiftT n m] (x : n α) :
(monadLift x : ExceptT ε m α).run = Except.ok < > (monadLift x : m α) :=
  rfl

end ExceptT
