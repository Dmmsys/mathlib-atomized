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

/--
Instance `instIsOrderedAddMonoid` / 实例 `instIsOrderedAddMonoid`

English:
instance instIsOrderedAddMonoid
  signature: : IsOrderedAddMonoid Rat where
  body: fun _ _ ab _ => Rat.add_le_add_right.2 ab

中文:
实例 instIsOrderedAddMonoid
  签名: : 是OrderedAdd幺半群 有理数 where
  定义体: fun _ _ ab _ => Rat.add_le_add_right.2 ab

Depends on / 依赖: Rat.add_le_add_right, add_le_add_right
-/
instance instIsOrderedAddMonoid : IsOrderedAddMonoid Rat where
  add_le_add_left := fun _ _ ab _ => Rat.add_le_add_right.2 ab

/--
Instance `instIsStrictOrderedRing` / 实例 `instIsStrictOrderedRing`

English:
instance instIsStrictOrderedRing
  signature: : IsStrictOrderedRing Rat
  body: .of_mul_pos fun _ _ ha hb =>
  (Rat.mul_nonneg ha.le hb.le).lt_of_ne' (mul_ne_zero ha.ne' hb.ne')

中文:
实例 instIsStrictOrderedRing
  签名: : 是StrictOrdered环 有理数
  定义体: .of_mul_pos fun _ _ ha hb =>
  (Rat.mul_nonneg ha.le hb.le).lt_of_ne' (mul_ne_zero ha.ne' hb.ne')

Depends on / 依赖: of_mul_pos
-/
instance instIsStrictOrderedRing : IsStrictOrderedRing Rat := .of_mul_pos fun _ _ ha hb =>
  (Rat.mul_nonneg ha.le hb.le).lt_of_ne' (mul_ne_zero ha.ne' hb.ne')

end Rat
