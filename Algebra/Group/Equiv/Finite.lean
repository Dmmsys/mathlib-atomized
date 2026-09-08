/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Data.Fintype.Defs

/-!
# Finite types with addition/multiplications

This file contains basic results and instances for finite types that have an
addition/multiplication operator.

## Main results

* `Fintype.decidableEqMulEquivFintype`: `MulEquiv`s on finite types have decidable equality
-/

public section

assert_not_exists MonoidWithZero MulAction

open Function

universe u v

variable {α β γ : Type*}

namespace Fintype

section BundledHoms

@[to_additive]
/-
**Fintype.decidableEqMulEquivFintype** 是 Mathlib 中的一个实例，位于命名空间 `Fintype`。
形式化陈述：decidableEqMulEquivFintype {α β : Type*} [DecidableEq β] [Fintype α] [Mul 
α] [Mul β] : DecidableEq (α ≃* β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableEqMulEquivFintype {α β : Type*} [DecidableEq β] [Fintype α] [Mul α] [Mul β] :
    DecidableEq (α ≃* β) :=
  fun a b => decidable_of_iff ((a : α → β) = b) (Injective.eq_iff DFunLike.coe_injective)

end BundledHoms

end Fintype

