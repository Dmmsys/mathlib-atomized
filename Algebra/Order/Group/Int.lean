/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Order.Monoid.Defs

/-!
# The integers form a linear ordered group

This file contains the instance necessary to show that the integers are a linear ordered
additive group.

See note [foundational algebra order theory].
-/

public section

-- We should need only a minimal development of sets in order to get here.
assert_not_exists Set.Subsingleton Ring

/-
**Int.instIsOrderedAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Int.instIsOrderedAddMonoid : IsOrderedAddMonoid Int where add_le_add_left 
_ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.add_le_add_right`：∀ {a b : ℤ}, a ≤ b → ∀ (c : ℤ), a + c ≤ b + c
-/
instance Int.instIsOrderedAddMonoid : IsOrderedAddMonoid ℤ where
  add_le_add_left _ _ := Int.add_le_add_right
