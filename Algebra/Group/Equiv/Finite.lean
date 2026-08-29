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
/--
Instance `decidableEqMulEquivFintype` / 实例 `decidableEqMulEquivFintype`

English:
instance decidableEqMulEquivFintype
  signature: {α β : Type*} [DecidableEq β] [Fintype α] [Mul α] [Mul β]
  body: fun a b => decidable_of_iff ((a : α -> β) = b) (Injective.eq_iff DFunLike.coe_injective)

中文:
实例 decidableEqMulEquivFintype
  签名: {α β : 类型} [DecidableEq β] [Fintype α] [Mul α] [Mul β]
  定义体: fun a b => decidable_of_iff ((a : α -> β) = b) (Injective.eq_iff DFunLike.coe_injective)

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Injective, Injective.eq_iff, coe_injective, decidable_of_iff, eq_iff
-/
instance decidableEqMulEquivFintype {α β : Type*} [DecidableEq β] [Fintype α] [Mul α] [Mul β] :
    DecidableEq (α ≃* β) :=
  fun a b => decidable_of_iff ((a : α -> β) = b) (Injective.eq_iff DFunLike.coe_injective)

end BundledHoms

end Fintype
