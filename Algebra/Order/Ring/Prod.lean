/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Prod

/-!
# Products of ordered rings
-/

public section

variable {α β : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: α] [PartialOrder α] [IsOrderedRing α]
  body: ⟨zero_le_one, zero_le_one⟩
  mul_le_mul_of_nonneg_left _a ha _b _c hbc :=
    ⟨mul_le_mul_of_nonneg_left hbc.1 ha.1, mul_le_mul_of_nonneg_left hbc.2 ha.2⟩
  mul_le_mul_of_nonneg_right _a ha _b _c hbc :=
    ⟨mul_le_mul_of_nonneg_right hbc.1 ha.1, mul_le_mul_of_nonneg_right hbc.2 ha.2⟩

中文:
实例 [半环
  签名: α] [偏序 α] [是Ordered环 α]
  定义体: ⟨zero_le_one, zero_le_one⟩
  mul_le_mul_of_nonneg_left _a ha _b _c hbc :=
    ⟨mul_le_mul_of_nonneg_left hbc.1 ha.1, mul_le_mul_of_nonneg_left hbc.2 ha.2⟩
  mul_le_mul_of_nonneg_right _a ha _b _c hbc :=
    ⟨mul_le_mul_of_nonneg_right hbc.1 ha.1, mul_le_mul_of_nonneg_right hbc.2 ha.2⟩

Depends on / 依赖: zero_le_one
-/
instance [Semiring α] [PartialOrder α] [IsOrderedRing α]
    [Semiring β] [PartialOrder β] [IsOrderedRing β] : IsOrderedRing (α × β) where
  zero_le_one := ⟨zero_le_one, zero_le_one⟩
  mul_le_mul_of_nonneg_left _a ha _b _c hbc :=
    ⟨mul_le_mul_of_nonneg_left hbc.1 ha.1, mul_le_mul_of_nonneg_left hbc.2 ha.2⟩
  mul_le_mul_of_nonneg_right _a ha _b _c hbc :=
    ⟨mul_le_mul_of_nonneg_right hbc.1 ha.1, mul_le_mul_of_nonneg_right hbc.2 ha.2⟩
