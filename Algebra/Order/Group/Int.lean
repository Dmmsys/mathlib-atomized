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

/--
Instance `Int.instIsOrderedAddMonoid` / 实例 `Int.instIsOrderedAddMonoid`

English:
instance Int.instIsOrderedAddMonoid
  signature: : IsOrderedAddMonoid Int where
  body: Int.add_le_add_right

中文:
实例 整数.instIsOrderedAddMonoid
  签名: : 是OrderedAdd幺半群 整数 where
  定义体: Int.add_le_add_right

Depends on / 依赖: Int.add_le_add_right, add_le_add_right
-/
instance Int.instIsOrderedAddMonoid : IsOrderedAddMonoid Int where
  add_le_add_left _ _ := Int.add_le_add_right
