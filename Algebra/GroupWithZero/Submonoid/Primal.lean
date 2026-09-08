/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Divisibility

/-!
# Submonoid of primal elements
-/

@[expose] public section

assert_not_exists RelIso Ring

/-- The submonoid of primal elements in a cancellative commutative monoid with zero. -/
/-
**Submonoid.isPrimal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submonoid.isPrimal (M₀ : Type*) [CommMonoidWithZero M₀] [IsCancelMulZero M
₀] : Submonoid M₀ where carrier
参数：M₀ : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrimal.mul`：IsPrimal.mul {α} [CommMonoidWithZero α] [IsCancelMulZero α
] {m n : α} (hm : IsPrimal m) (hn : IsPrimal n) : IsPrimal (m * n)

--- 原说明 ---
The submonoid of primal elements in a cancellative commutative monoid with zero.
-/
def Submonoid.isPrimal (M₀ : Type*) [CommMonoidWithZero M₀] [IsCancelMulZero M₀] :
    Submonoid M₀ where
  carrier := {a | IsPrimal a}
  mul_mem' := .mul
  one_mem' := isUnit_one.isPrimal
