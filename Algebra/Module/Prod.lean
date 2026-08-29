/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Prod
public import Mathlib.Algebra.Module.Defs

/-!
# Prod instances for module and multiplicative actions

This file defines instances for binary product of modules
-/

public section


variable {R : Type*} {M : Type*} {N : Type*}

namespace Prod

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
  body: by ext <;> exact add_smul ..
  zero_smul _ := by ext <;> exact zero_smul ..

中文:
实例 instModule
  签名: [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
  定义体: by ext <;> exact add_smul ..
  zero_smul _ := by ext <;> exact zero_smul ..

Depends on / 依赖: add_smul, zero_smul
-/
instance instModule [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] :
    Module R (M × N) where
  add_smul _ _ _ := by ext <;> exact add_smul ..
  zero_smul _ := by ext <;> exact zero_smul ..

end Prod
