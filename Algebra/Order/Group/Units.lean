/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Units

/-!
# The units of an ordered commutative monoid form an ordered commutative group
-/

public section


variable {α : Type*}

/-- The units of an ordered commutative monoid form an ordered commutative group. -/
@[to_additive
      /-- The units of an ordered commutative additive monoid form an ordered commutative
      additive group. -/]
/--
Instance `Units.isOrderedMonoid` / 实例 `Units.isOrderedMonoid`

English:
instance Units.isOrderedMonoid
  signature: [CommMonoid α] [Preorder α] [IsOrderedMonoid α]
  body: mul_le_mul_left (α := α) h _

中文:
实例 单位群.isOrderedMonoid
  签名: [交换幺半群 α] [预序 α] [是Ordered幺半群 α]
  定义体: mul_le_mul_left (α := α) h _

Depends on / 依赖: mul_le_mul_left
-/
instance Units.isOrderedMonoid [CommMonoid α] [Preorder α] [IsOrderedMonoid α] :
    IsOrderedMonoid αˣ where
  mul_le_mul_left _ _ h _ := mul_le_mul_left (α := α) h _
