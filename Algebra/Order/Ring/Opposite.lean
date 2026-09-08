/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Group.Opposite
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Opposite

/-!
# Ordered ring instances for `MulOpposite`/`AddOpposite`

This file transfers ordered (semi)ring instances from `R` to `Rᵐᵒᵖ` and `Rᵃᵒᵖ`.
-/

public section

variable {R : Type*}

namespace MulOpposite

/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring R] [PartialOrder R] [IsOrderedRing R] : IsOrderedRing Rᵐᵒᵖ where
  zero_le_one := zero_le_one (α := R)
  mul_le_mul_of_nonneg_left _a ha _b _c hbc := mul_le_mul_of_nonneg_right (α := R) hbc ha
  mul_le_mul_of_nonneg_right _a ha _b _c hbc := mul_le_mul_of_nonneg_left (α := R) hbc ha

end MulOpposite

namespace AddOpposite

/-
**AddOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring R] [PartialOrder R] [IsOrderedRing R] : IsOrderedRing Rᵃᵒᵖ where
  zero_le_one := zero_le_one (α := R)
  mul_le_mul_of_nonneg_left _a ha _b _c hbc := mul_le_mul_of_nonneg_left (α := R) hbc ha
  mul_le_mul_of_nonneg_right _a ha _b _c hbc := mul_le_mul_of_nonneg_right (α := R) hbc ha

end AddOpposite

