/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Ring.Rat

/-!
# The rational numbers form a linear ordered commutative ring

This file proves that the linear order on `ℚ` makes it into an ordered ring.

`ℚ` is in fact a linearly ordered field. To access this fact, one must also import
`Mathlib/Algebra/Field/Rat.lean`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, order, ordering
-/

public section

assert_not_exists Field Finset Set.Icc GaloisConnection

namespace Rat

/-
**Rat.instIsOrderedAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：instIsOrderedAddMonoid : IsOrderedAddMonoid Rat where add_le_add_left
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rat.add_le_add_right`：∀ {a b c : ℚ}, a + c ≤ b + c ↔ a ≤ b
-/
instance instIsOrderedAddMonoid : IsOrderedAddMonoid ℚ where
  add_le_add_left := fun _ _ ab _ => Rat.add_le_add_right.2 ab
/-
**Rat.instIsStrictOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：instIsStrictOrderedRing : IsStrictOrderedRing Rat
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `IsStrictOrderedRing.of_mul_pos`：IsStrictOrderedRing.of_mul_pos [Ring R] 
[PartialOrder R] [IsOrderedAddMonoid R] [ZeroLEOneClass R] [Nontrivial R] (mul_p
os : forall a b : R,…
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `Rat.mul_nonneg`：∀ {a b : ℚ}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
instance instIsStrictOrderedRing : IsStrictOrderedRing ℚ := .of_mul_pos fun _ _ ha hb ↦
  (Rat.mul_nonneg ha.le hb.le).lt_of_ne' (mul_ne_zero ha.ne' hb.ne')

end Rat

