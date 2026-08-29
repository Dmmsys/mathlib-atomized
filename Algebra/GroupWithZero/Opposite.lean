/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.GroupWithZero.InjSurj
public import Mathlib.Algebra.GroupWithZero.NeZero

/-!
# Opposites of groups with zero
-/

public section

assert_not_exists Ring

variable {α : Type*}

namespace MulOpposite

/--
Instance `instMulZeroClass` / 实例 `instMulZeroClass`

English:
instance instMulZeroClass
  signature: [MulZeroClass α]
  body: unop_injective mul_zero _
mul_zero _ := unop_injective zero_mul _

中文:
实例 instMulZeroClass
  签名: [MulZeroClass α]
  定义体: unop_injective mul_zero _
mul_zero _ := unop_injective zero_mul _

Depends on / 依赖: mul_zero, unop_injective
-/
instance instMulZeroClass [MulZeroClass α] : MulZeroClass αᵐᵒᵖ where
zero_mul _ := unop_injective mul_zero _
mul_zero _ := unop_injective zero_mul _

/--
Instance `instMulZeroOneClass` / 实例 `instMulZeroOneClass`

English:
instance instMulZeroOneClass
  signature: [MulZeroOneClass α]
  body: instMulOneClass
  __ := instMulZeroClass

中文:
实例 instMulZeroOneClass
  签名: [MulZeroOneClass α]
  定义体: instMulOneClass
  __ := instMulZeroClass

Depends on / 依赖: instMulOneClass
-/
instance instMulZeroOneClass [MulZeroOneClass α] : MulZeroOneClass αᵐᵒᵖ where
  __ := instMulOneClass
  __ := instMulZeroClass

/--
Instance `instSemigroupWithZero` / 实例 `instSemigroupWithZero`

English:
instance instSemigroupWithZero
  signature: [SemigroupWithZero α]
  body: instSemigroup
  __ := instMulZeroClass

中文:
实例 instSemigroupWithZero
  签名: [SemigroupWithZero α]
  定义体: instSemigroup
  __ := instMulZeroClass

Depends on / 依赖: instSemigroup
-/
instance instSemigroupWithZero [SemigroupWithZero α] : SemigroupWithZero αᵐᵒᵖ where
  __ := instSemigroup
  __ := instMulZeroClass

/--
Instance `instMonoidWithZero` / 实例 `instMonoidWithZero`

English:
instance instMonoidWithZero
  signature: [MonoidWithZero α]
  body: instMonoid
  __ := instMulZeroOneClass

中文:
实例 instMonoidWithZero
  签名: [MonoidWithZero α]
  定义体: instMonoid
  __ := instMulZeroOneClass

Depends on / 依赖: instMonoid
-/
instance instMonoidWithZero [MonoidWithZero α] : MonoidWithZero αᵐᵒᵖ where
  __ := instMonoid
  __ := instMulZeroOneClass

/--
Instance `instGroupWithZero` / 实例 `instGroupWithZero`

English:
instance instGroupWithZero
  signature: [GroupWithZero α]
  body: instMonoidWithZero
  __ := instNontrivial
  __ := instDivInvMonoid
mul_inv_cancel _ hx := unop_injective inv_mul_cancel₀ unop_injective.ne hx
  inv_zero := unop_injective inv_zero

中文:
实例 instGroupWithZero
  签名: [GroupWithZero α]
  定义体: instMonoidWithZero
  __ := instNontrivial
  __ := instDivInvMonoid
mul_inv_cancel _ hx := unop_injective inv_mul_cancel₀ unop_injective.ne hx
  inv_zero := unop_injective inv_zero

Depends on / 依赖: instMonoidWithZero
-/
instance instGroupWithZero [GroupWithZero α] : GroupWithZero αᵐᵒᵖ where
  __ := instMonoidWithZero
  __ := instNontrivial
  __ := instDivInvMonoid
mul_inv_cancel _ hx := unop_injective inv_mul_cancel₀ unop_injective.ne hx
  inv_zero := unop_injective inv_zero

/--
Instance `instNoZeroDivisors` / 实例 `instNoZeroDivisors`

English:
instance instNoZeroDivisors
  signature: [Zero α] [Mul α] [NoZeroDivisors α]
  body: Or.casesOn (eq_zero_or_eq_zero_of_mul_eq_zero <| op_injective H)
(fun hy => Or.inr <| unop_injective <| hy) fun hx => Or.inl unop_injective hx

中文:
实例 instNoZeroDivisors
  签名: [Zero α] [Mul α] [NoZeroDivisors α]
  定义体: Or.casesOn (eq_zero_or_eq_zero_of_mul_eq_zero <| op_injective H)
(fun hy => Or.inr <| unop_injective <| hy) fun hx => Or.inl unop_injective hx

Depends on / 依赖: Or.casesOn, Or.inl, Or.inr, casesOn, eq_zero_or_eq_zero_of_mul_eq_zero, op_injective, unop_injective
-/
instance instNoZeroDivisors [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors αᵐᵒᵖ where
  eq_zero_or_eq_zero_of_mul_eq_zero (H : op (_ * _) = op (0 : α)) :=
      Or.casesOn (eq_zero_or_eq_zero_of_mul_eq_zero <| op_injective H)
(fun hy => Or.inr <| unop_injective <| hy) fun hx => Or.inl unop_injective hx

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [Zero α] [IsLeftCancelMulZero α] : IsRightCancelMulZero αᵐᵒᵖ where
  body: unop_injective
    mul_left_cancel₀ (unop_injective.ne_iff.mpr h) (congr_arg unop eq)

中文:
实例 [Mul
  签名: α] [Zero α] [IsLeftCancelMulZero α] : IsRightCancelMulZero αᵐᵒᵖ where
  定义体: unop_injective
    mul_left_cancel₀ (unop_injective.ne_iff.mpr h) (congr_arg unop eq)

Depends on / 依赖: unop_injective
-/
instance [Mul α] [Zero α] [IsLeftCancelMulZero α] : IsRightCancelMulZero αᵐᵒᵖ where
mul_right_cancel_of_ne_zero h _ _ eq := unop_injective
    mul_left_cancel₀ (unop_injective.ne_iff.mpr h) (congr_arg unop eq)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [Zero α] [IsRightCancelMulZero α] : IsLeftCancelMulZero αᵐᵒᵖ where
  body: unop_injective
    mul_right_cancel₀ (unop_injective.ne_iff.mpr h) (congr_arg unop eq)

中文:
实例 [Mul
  签名: α] [Zero α] [IsRightCancelMulZero α] : IsLeftCancelMulZero αᵐᵒᵖ where
  定义体: unop_injective
    mul_right_cancel₀ (unop_injective.ne_iff.mpr h) (congr_arg unop eq)

Depends on / 依赖: unop_injective
-/
instance [Mul α] [Zero α] [IsRightCancelMulZero α] : IsLeftCancelMulZero αᵐᵒᵖ where
mul_left_cancel_of_ne_zero h _ _ eq := unop_injective
    mul_right_cancel₀ (unop_injective.ne_iff.mpr h) (congr_arg unop eq)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [Zero α] [IsCancelMulZero α] : IsCancelMulZero αᵐᵒᵖ where

中文:
实例 [Mul
  签名: α] [Zero α] [IsCancelMulZero α] : IsCancelMulZero αᵐᵒᵖ where

Depends on / 依赖: nullHomotopicMap, nullHomotopicMap_comp, split_ifs, zero_comp
-/
instance [Mul α] [Zero α] [IsCancelMulZero α] : IsCancelMulZero αᵐᵒᵖ where

/--
theorem `isLeftCancelMulZero_iff` / 定理 `isLeftCancelMulZero_iff`

English:
theorem isLeftCancelMulZero_iff
  given: [Mul α] [Zero α]
  proof: (op_injective.comp op_injective).isRightCancelMulZero _ rfl fun _ _ => rfl
  mpr _ := inferInstance

中文:
定理 isLeftCancelMulZero_iff
  条件: [Mul α] [Zero α]
  证明: (op_injective.comp op_injective).isRightCancelMulZero _ rfl fun _ _ => rfl
  mpr _ := inferInstance
-/
@[simp] theorem isLeftCancelMulZero_iff [Mul α] [Zero α] :
    IsLeftCancelMulZero αᵐᵒᵖ ↔ IsRightCancelMulZero α where
  mp _ := (op_injective.comp op_injective).isRightCancelMulZero _ rfl fun _ _ => rfl
  mpr _ := inferInstance

/--
theorem `isRightCancelMulZero_iff` / 定理 `isRightCancelMulZero_iff`

English:
theorem isRightCancelMulZero_iff
  given: [Mul α] [Zero α]
  proof: (op_injective.comp op_injective).isLeftCancelMulZero _ rfl fun _ _ => rfl
  mpr _ := inferInstance

中文:
定理 isRightCancelMulZero_iff
  条件: [Mul α] [Zero α]
  证明: (op_injective.comp op_injective).isLeftCancelMulZero _ rfl fun _ _ => rfl
  mpr _ := inferInstance
-/
@[simp] theorem isRightCancelMulZero_iff [Mul α] [Zero α] :
    IsRightCancelMulZero αᵐᵒᵖ ↔ IsLeftCancelMulZero α where
  mp _ := (op_injective.comp op_injective).isLeftCancelMulZero _ rfl fun _ _ => rfl
  mpr _ := inferInstance

/--
theorem `isCancelMulZero_iff` / 定理 `isCancelMulZero_iff`

English:
theorem isCancelMulZero_iff
  given: [Mul α] [Zero α]
  proof: (op_injective.comp op_injective).isCancelMulZero _ rfl fun _ _ => rfl
  mpr _ := inferInstance

中文:
定理 isCancelMulZero_iff
  条件: [Mul α] [Zero α]
  证明: (op_injective.comp op_injective).isCancelMulZero _ rfl fun _ _ => rfl
  mpr _ := inferInstance
-/
@[simp] theorem isCancelMulZero_iff [Mul α] [Zero α] :
    IsCancelMulZero αᵐᵒᵖ ↔ IsCancelMulZero α where
  mp _ := (op_injective.comp op_injective).isCancelMulZero _ rfl fun _ _ => rfl
  mpr _ := inferInstance

end MulOpposite

namespace AddOpposite

/--
Instance `instMulZeroClass` / 实例 `instMulZeroClass`

English:
instance instMulZeroClass
  signature: [MulZeroClass α]
  body: unop_injective zero_mul _
mul_zero _ := unop_injective mul_zero _

中文:
实例 instMulZeroClass
  签名: [MulZeroClass α]
  定义体: unop_injective zero_mul _
mul_zero _ := unop_injective mul_zero _

Depends on / 依赖: unop_injective, zero_mul
-/
instance instMulZeroClass [MulZeroClass α] : MulZeroClass αᵃᵒᵖ where
zero_mul _ := unop_injective zero_mul _
mul_zero _ := unop_injective mul_zero _

/--
Instance `instMulZeroOneClass` / 实例 `instMulZeroOneClass`

English:
instance instMulZeroOneClass
  signature: [MulZeroOneClass α]
  body: instMulOneClass
  __ := instMulZeroClass

中文:
实例 instMulZeroOneClass
  签名: [MulZeroOneClass α]
  定义体: instMulOneClass
  __ := instMulZeroClass

Depends on / 依赖: instMulOneClass
-/
instance instMulZeroOneClass [MulZeroOneClass α] : MulZeroOneClass αᵃᵒᵖ where
  __ := instMulOneClass
  __ := instMulZeroClass

/--
Instance `instSemigroupWithZero` / 实例 `instSemigroupWithZero`

English:
instance instSemigroupWithZero
  signature: [SemigroupWithZero α]
  body: instSemigroup
  __ := instMulZeroClass

中文:
实例 instSemigroupWithZero
  签名: [SemigroupWithZero α]
  定义体: instSemigroup
  __ := instMulZeroClass

Depends on / 依赖: instSemigroup
-/
instance instSemigroupWithZero [SemigroupWithZero α] : SemigroupWithZero αᵃᵒᵖ where
  __ := instSemigroup
  __ := instMulZeroClass

/--
Instance `instMonoidWithZero` / 实例 `instMonoidWithZero`

English:
instance instMonoidWithZero
  signature: [MonoidWithZero α]
  body: instMonoid
  __ := instMulZeroOneClass

中文:
实例 instMonoidWithZero
  签名: [MonoidWithZero α]
  定义体: instMonoid
  __ := instMulZeroOneClass

Depends on / 依赖: instMonoid
-/
instance instMonoidWithZero [MonoidWithZero α] : MonoidWithZero αᵃᵒᵖ where
  __ := instMonoid
  __ := instMulZeroOneClass

/--
Instance `instNoZeroDivisors` / 实例 `instNoZeroDivisors`

English:
instance instNoZeroDivisors
  signature: [Zero α] [Mul α] [NoZeroDivisors α]
  body: Or.imp (fun hx => unop_injective hx) (fun hy => unop_injective hy)
    (@eq_zero_or_eq_zero_of_mul_eq_zero α _ _ _ _ _ <| op_injective H)

中文:
实例 instNoZeroDivisors
  签名: [Zero α] [Mul α] [NoZeroDivisors α]
  定义体: Or.imp (fun hx => unop_injective hx) (fun hy => unop_injective hy)
    (@eq_zero_or_eq_zero_of_mul_eq_zero α _ _ _ _ _ <| op_injective H)

Depends on / 依赖: Or.imp, eq_zero_or_eq_zero_of_mul_eq_zero, nullHomotopicMap, nullHomotopicMap_f, op_injective, split_ifs, unop_injective
-/
instance instNoZeroDivisors [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors αᵃᵒᵖ where
  eq_zero_or_eq_zero_of_mul_eq_zero (H : op (_ * _) = op (0 : α)) :=
    Or.imp (fun hx => unop_injective hx) (fun hy => unop_injective hy)
    (@eq_zero_or_eq_zero_of_mul_eq_zero α _ _ _ _ _ <| op_injective H)

/--
Instance `instGroupWithZero` / 实例 `instGroupWithZero`

English:
instance instGroupWithZero
  signature: [GroupWithZero α]
  body: instMonoidWithZero
  __ := instNontrivial
  __ := instDivInvMonoid
mul_inv_cancel _ hx := unop_injective mul_inv_cancel₀ unop_injective.ne hx
  inv_zero := unop_injective inv_zero

中文:
实例 instGroupWithZero
  签名: [GroupWithZero α]
  定义体: instMonoidWithZero
  __ := instNontrivial
  __ := instDivInvMonoid
mul_inv_cancel _ hx := unop_injective mul_inv_cancel₀ unop_injective.ne hx
  inv_zero := unop_injective inv_zero

Depends on / 依赖: instMonoidWithZero
-/
instance instGroupWithZero [GroupWithZero α] : GroupWithZero αᵃᵒᵖ where
  __ := instMonoidWithZero
  __ := instNontrivial
  __ := instDivInvMonoid
mul_inv_cancel _ hx := unop_injective mul_inv_cancel₀ unop_injective.ne hx
  inv_zero := unop_injective inv_zero

end AddOpposite
