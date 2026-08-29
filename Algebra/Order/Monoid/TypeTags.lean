/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/-! # Bundled ordered monoid structures on `Multiplicative α` and `Additive α`. -/

public section

variable {α : Type*}

/--
Instance `Multiplicative.isOrderedMonoid` / 实例 `Multiplicative.isOrderedMonoid`

English:
instance Multiplicative.isOrderedMonoid
  signature: [AddCommMonoid α] [Preorder α] [IsOrderedAddMonoid α]
  body: { mul_le_mul_left := @IsOrderedAddMonoid.add_le_add_left α _ _ _ }

中文:
实例 Multiplicative.isOrderedMonoid
  签名: [AddCommMonoid α] [Preorder α] [IsOrderedAddMonoid α]
  定义体: { mul_le_mul_left := @IsOrderedAddMonoid.add_le_add_left α _ _ _ }

Depends on / 依赖: IsOrderedAddMonoid, IsOrderedAddMonoid.add_le_add_left, add_le_add_left, mul_le_mul_left
-/
instance Multiplicative.isOrderedMonoid [AddCommMonoid α] [Preorder α] [IsOrderedAddMonoid α] :
    IsOrderedMonoid (Multiplicative α) :=
  { mul_le_mul_left := @IsOrderedAddMonoid.add_le_add_left α _ _ _ }

/--
Instance `Additive.isOrderedAddMonoid` / 实例 `Additive.isOrderedAddMonoid`

English:
instance Additive.isOrderedAddMonoid
  signature: [CommMonoid α] [Preorder α] [IsOrderedMonoid α]
  body: { add_le_add_left := @IsOrderedMonoid.mul_le_mul_left α _ _ _ }

中文:
实例 Additive.isOrderedAddMonoid
  签名: [CommMonoid α] [Preorder α] [IsOrderedMonoid α]
  定义体: { add_le_add_left := @IsOrderedMonoid.mul_le_mul_left α _ _ _ }

Depends on / 依赖: IsOrderedMonoid, IsOrderedMonoid.mul_le_mul_left, add_le_add_left, mul_le_mul_left
-/
instance Additive.isOrderedAddMonoid [CommMonoid α] [Preorder α] [IsOrderedMonoid α] :
    IsOrderedAddMonoid (Additive α) :=
  { add_le_add_left := @IsOrderedMonoid.mul_le_mul_left α _ _ _ }

/--
Instance `Multiplicative.isOrderedCancelMonoid` / 实例 `Multiplicative.isOrderedCancelMonoid`

English:
instance Multiplicative.isOrderedCancelMonoid
  body: { le_of_mul_le_mul_left := @IsOrderedCancelAddMonoid.le_of_add_le_add_left α _ _ _ }

中文:
实例 Multiplicative.isOrderedCancelMonoid
  定义体: { le_of_mul_le_mul_left := @IsOrderedCancelAddMonoid.le_of_add_le_add_left α _ _ _ }

Depends on / 依赖: IsOrderedCancelAddMonoid, IsOrderedCancelAddMonoid.le_of_add_le_add_left, le_of_add_le_add_left, le_of_mul_le_mul_left
-/
instance Multiplicative.isOrderedCancelMonoid
    [AddCommMonoid α] [Preorder α] [IsOrderedCancelAddMonoid α] :
    IsOrderedCancelMonoid (Multiplicative α) :=
  { le_of_mul_le_mul_left := @IsOrderedCancelAddMonoid.le_of_add_le_add_left α _ _ _ }

/--
Instance `Additive.isOrderedCancelAddMonoid` / 实例 `Additive.isOrderedCancelAddMonoid`

English:
instance Additive.isOrderedCancelAddMonoid
  body: { le_of_add_le_add_left := @IsOrderedCancelMonoid.le_of_mul_le_mul_left α _ _ _ }

中文:
实例 Additive.isOrderedCancelAddMonoid
  定义体: { le_of_add_le_add_left := @IsOrderedCancelMonoid.le_of_mul_le_mul_left α _ _ _ }

Depends on / 依赖: IsOrderedCancelMonoid, IsOrderedCancelMonoid.le_of_mul_le_mul_left, le_of_add_le_add_left, le_of_mul_le_mul_left
-/
instance Additive.isOrderedCancelAddMonoid
    [CommMonoid α] [Preorder α] [IsOrderedCancelMonoid α] :
    IsOrderedCancelAddMonoid (Additive α) :=
  { le_of_add_le_add_left := @IsOrderedCancelMonoid.le_of_mul_le_mul_left α _ _ _ }

/--
Instance `Multiplicative.canonicallyOrderedMul` / 实例 `Multiplicative.canonicallyOrderedMul`

English:
instance Multiplicative.canonicallyOrderedMul
  body: le_add_self (α := α)
  le_self_mul _ _ := le_self_add (α := α)

中文:
实例 Multiplicative.canonicallyOrderedMul
  定义体: le_add_self (α := α)
  le_self_mul _ _ := le_self_add (α := α)

Depends on / 依赖: le_add_self
-/
instance Multiplicative.canonicallyOrderedMul
    [AddMonoid α] [Preorder α] [CanonicallyOrderedAdd α] :
    CanonicallyOrderedMul (Multiplicative α) where
  le_mul_self _ _ := le_add_self (α := α)
  le_self_mul _ _ := le_self_add (α := α)

/--
Instance `Additive.canonicallyOrderedAdd` / 实例 `Additive.canonicallyOrderedAdd`

English:
instance Additive.canonicallyOrderedAdd
  body: le_mul_self (α := α)
  le_self_add _ _ := le_self_mul (α := α)

中文:
实例 Additive.canonicallyOrderedAdd
  定义体: le_mul_self (α := α)
  le_self_add _ _ := le_self_mul (α := α)

Depends on / 依赖: le_mul_self
-/
instance Additive.canonicallyOrderedAdd
    [Monoid α] [Preorder α] [CanonicallyOrderedMul α] :
    CanonicallyOrderedAdd (Additive α) where
  le_add_self _ _ := le_mul_self (α := α)
  le_self_add _ _ := le_self_mul (α := α)
