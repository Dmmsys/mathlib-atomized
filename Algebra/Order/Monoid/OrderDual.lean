/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Group.Synonym
public import Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual
public import Mathlib.Algebra.Order.Monoid.Defs

/-! # Ordered monoid structures on the order dual. -/

public section

universe u

variable {α : Type u}

open Function

namespace OrderDual

@[to_additive]
/--
Instance `isOrderedMonoid` / 实例 `isOrderedMonoid`

English:
instance isOrderedMonoid
  signature: [CommMonoid α] [Preorder α] [IsOrderedMonoid α]
  body: mul_le_mul_left h c

@[to_additive]

中文:
实例 isOrderedMonoid
  签名: [交换幺半群 α] [预序 α] [是Ordered幺半群 α]
  定义体: mul_le_mul_left h c

@[to_additive]

Depends on / 依赖: mul_le_mul_left
-/
instance isOrderedMonoid [CommMonoid α] [Preorder α] [IsOrderedMonoid α] :
    IsOrderedMonoid αᵒᵈ where
  mul_le_mul_left _ _ h c := mul_le_mul_left h c

@[to_additive]
/--
Instance `isOrderedCancelMonoid` / 实例 `isOrderedCancelMonoid`

English:
instance isOrderedCancelMonoid
  signature: [CommMonoid α] [Preorder α] [IsOrderedCancelMonoid α]
  body: le_of_mul_le_mul_left'

中文:
实例 isOrderedCancelMonoid
  签名: [交换幺半群 α] [预序 α] [是OrderedCancel幺半群 α]
  定义体: le_of_mul_le_mul_left'

Depends on / 依赖: le_of_mul_le_mul_left
-/
instance isOrderedCancelMonoid [CommMonoid α] [Preorder α] [IsOrderedCancelMonoid α] :
    IsOrderedCancelMonoid αᵒᵈ where
  le_of_mul_le_mul_left _ _ _ := le_of_mul_le_mul_left'

end OrderDual
