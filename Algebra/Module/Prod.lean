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

/-
**Prod.instModule** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：instModule [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [
Module R N] : Module R (M × N) where add_smul _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] :
    Module R (M × N) where
  add_smul _ _ _ := by ext <;> exact add_smul ..
  zero_smul _ := by ext <;> exact zero_smul ..

end Prod

