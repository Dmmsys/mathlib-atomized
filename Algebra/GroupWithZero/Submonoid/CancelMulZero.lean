/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
module

public import Mathlib.Algebra.GroupWithZero.InjSurj
public import Mathlib.Algebra.Group.Submonoid.Defs

/-!
# Submagmas with zero inherit cancellations
-/

public section

namespace MulZeroMemClass

variable {M₀ : Type*} [Mul M₀] [Zero M₀] {S : Type*} [SetLike S M₀] [MulMemClass S M₀]
  [ZeroMemClass S M₀] (s : S)

/--
Instance `isLeftCancelMulZero` / 实例 `isLeftCancelMulZero`

English:
instance isLeftCancelMulZero
  signature: [IsLeftCancelMulZero M₀]
  body: Subtype.coe_injective.isLeftCancelMulZero Subtype.val rfl fun _ _ => rfl

中文:
实例 isLeftCancelMulZero
  签名: [是左消去MulZero M₀]
  定义体: Subtype.coe_injective.isLeftCancelMulZero Subtype.val rfl fun _ _ => rfl

Depends on / 依赖: Subtype, Subtype.coe_injective.isLeftCancelMulZero, Subtype.val, coe_injective, isLeftCancelMulZero
-/
instance isLeftCancelMulZero [IsLeftCancelMulZero M₀] : IsLeftCancelMulZero s :=
  Subtype.coe_injective.isLeftCancelMulZero Subtype.val rfl fun _ _ => rfl

/--
Instance `isRightCancelMulZero` / 实例 `isRightCancelMulZero`

English:
instance isRightCancelMulZero
  signature: [IsRightCancelMulZero M₀]
  body: Subtype.coe_injective.isRightCancelMulZero Subtype.val rfl fun _ _ => rfl

中文:
实例 isRightCancelMulZero
  签名: [是右消去MulZero M₀]
  定义体: Subtype.coe_injective.isRightCancelMulZero Subtype.val rfl fun _ _ => rfl

Depends on / 依赖: Subtype, Subtype.coe_injective.isRightCancelMulZero, Subtype.val, coe_injective, infer_instance, isRightCancelMulZero
-/
instance isRightCancelMulZero [IsRightCancelMulZero M₀] : IsRightCancelMulZero s :=
  Subtype.coe_injective.isRightCancelMulZero Subtype.val rfl fun _ _ => rfl

/--
Instance `isCancelMulZero` / 实例 `isCancelMulZero`

English:
instance isCancelMulZero
  signature: [IsCancelMulZero M₀]

中文:
实例 isCancelMulZero
  签名: [是乘零消去 M₀]
-/
instance isCancelMulZero [IsCancelMulZero M₀] : IsCancelMulZero s where

end MulZeroMemClass
