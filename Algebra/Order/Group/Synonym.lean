/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Order.OrderDual
public import Mathlib.Order.Lex

/-!
# Group structure on the order type synonyms

Transfer algebraic instances from `α` to `αᵒᵈ`, `Lex α`, and `Colex α`.
-/

public section


open OrderDual

variable {α β : Type*}

/-! ### `OrderDual` -/

namespace OrderDual

set_option backward.inferInstanceAs.wrap.instances false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [One
  signature: α] : One αᵒᵈ
  body: inferInstanceAs One α

中文:
实例 [One
  签名: α] : One αᵒᵈ
  定义体: inferInstanceAs One α
-/
@[to_additive] instance [One α] : One αᵒᵈ := inferInstanceAs One α

set_option backward.inferInstanceAs.wrap.instances false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] : Mul αᵒᵈ
  body: inferInstanceAs Mul α

中文:
实例 [Mul
  签名: α] : Mul αᵒᵈ
  定义体: inferInstanceAs Mul α
-/
@[to_additive] instance [Mul α] : Mul αᵒᵈ := inferInstanceAs Mul α

set_option backward.inferInstanceAs.wrap.instances false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inv
  signature: α] : Inv αᵒᵈ
  body: inferInstanceAs Inv α

中文:
实例 [Inv
  签名: α] : Inv αᵒᵈ
  定义体: inferInstanceAs Inv α
-/
@[to_additive] instance [Inv α] : Inv αᵒᵈ := inferInstanceAs Inv α

set_option backward.inferInstanceAs.wrap.instances false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Div
  signature: α] : Div αᵒᵈ
  body: inferInstanceAs Div α

中文:
实例 [Div
  签名: α] : Div αᵒᵈ
  定义体: inferInstanceAs Div α
-/
@[to_additive] instance [Div α] : Div αᵒᵈ := inferInstanceAs Div α

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive (attr := to_additive) (reorder := 1 2) OrderDual.instSMul]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Pow
  signature: α β] : Pow αᵒᵈ β
  body: inferInstanceAs Pow α β

中文:
实例 [Pow
  签名: α β] : Pow αᵒᵈ β
  定义体: inferInstanceAs Pow α β
-/
instance [Pow α β] : Pow αᵒᵈ β := inferInstanceAs Pow α β

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive (attr := to_additive) (reorder := 1 2) OrderDual.instSMul']
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Pow
  signature: α β] : Pow α βᵒᵈ
  body: inferInstanceAs Pow α β

中文:
实例 [Pow
  签名: α β] : Pow α βᵒᵈ
  定义体: inferInstanceAs Pow α β
-/
instance [Pow α β] : Pow α βᵒᵈ := inferInstanceAs Pow α β

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semigroup
  signature: α] : Semigroup αᵒᵈ
  body: inferInstanceAs Semigroup α

中文:
实例 [Semigroup
  签名: α] : Semigroup αᵒᵈ
  定义体: inferInstanceAs Semigroup α
-/
@[to_additive] instance [Semigroup α] : Semigroup αᵒᵈ := inferInstanceAs Semigroup α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemigroup
  signature: α] : CommSemigroup αᵒᵈ
  body: inferInstanceAs CommSemigroup α

@[to_additive]

中文:
实例 [CommSemigroup
  签名: α] : CommSemigroup αᵒᵈ
  定义体: inferInstanceAs CommSemigroup α

@[to_additive]
-/
@[to_additive] instance [CommSemigroup α] : CommSemigroup αᵒᵈ := inferInstanceAs CommSemigroup α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [IsLeftCancelMul α] : IsLeftCancelMul αᵒᵈ
  body: inferInstanceAs IsLeftCancelMul α

@[to_additive]

中文:
实例 [Mul
  签名: α] [IsLeftCancelMul α] : IsLeftCancelMul αᵒᵈ
  定义体: inferInstanceAs IsLeftCancelMul α

@[to_additive]

Depends on / 依赖: IsLeftCancelMul
-/
instance [Mul α] [IsLeftCancelMul α] : IsLeftCancelMul αᵒᵈ :=
inferInstanceAs IsLeftCancelMul α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [IsRightCancelMul α] : IsRightCancelMul αᵒᵈ
  body: inferInstanceAs IsRightCancelMul α

@[to_additive]

中文:
实例 [Mul
  签名: α] [IsRightCancelMul α] : IsRightCancelMul αᵒᵈ
  定义体: inferInstanceAs IsRightCancelMul α

@[to_additive]

Depends on / 依赖: IsRightCancelMul
-/
instance [Mul α] [IsRightCancelMul α] : IsRightCancelMul αᵒᵈ :=
inferInstanceAs IsRightCancelMul α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [IsCancelMul α] : IsCancelMul αᵒᵈ where

中文:
实例 [Mul
  签名: α] [IsCancelMul α] : IsCancelMul αᵒᵈ where
-/
instance [Mul α] [IsCancelMul α] : IsCancelMul αᵒᵈ where

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LeftCancelSemigroup
  signature: α] : LeftCancelSemigroup αᵒᵈ where

中文:
实例 [LeftCancelSemigroup
  签名: α] : LeftCancelSemigroup αᵒᵈ where
-/
instance [LeftCancelSemigroup α] : LeftCancelSemigroup αᵒᵈ where

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RightCancelSemigroup
  signature: α] : RightCancelSemigroup αᵒᵈ where

中文:
实例 [RightCancelSemigroup
  签名: α] : RightCancelSemigroup αᵒᵈ where

Depends on / 依赖: IsOrderedMonoid, IsOrderedMonoid.toMulLeftMono, MulLeftMono, toMulLeftMono
-/
instance [RightCancelSemigroup α] : RightCancelSemigroup αᵒᵈ where

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulOneClass
  signature: α] : MulOneClass αᵒᵈ
  body: inferInstanceAs MulOneClass α

@[to_additive]

中文:
实例 [MulOneClass
  签名: α] : MulOneClass αᵒᵈ
  定义体: inferInstanceAs MulOneClass α

@[to_additive]

Depends on / 依赖: IsOrderedMonoid, IsOrderedMonoid.toMulRightMono, MulOneClass, MulRightMono, toMulRightMono
-/
instance [MulOneClass α] : MulOneClass αᵒᵈ := inferInstanceAs MulOneClass α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: α] : Monoid αᵒᵈ
  body: inferInstanceAs Monoid α

@[to_additive]

中文:
实例 [Monoid
  签名: α] : Monoid αᵒᵈ
  定义体: inferInstanceAs Monoid α

@[to_additive]

Depends on / 依赖: Monoid
-/
instance [Monoid α] : Monoid αᵒᵈ := inferInstanceAs Monoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommMonoid
  signature: α] : CommMonoid αᵒᵈ
  body: inferInstanceAs CommMonoid α

@[to_additive]

中文:
实例 [CommMonoid
  签名: α] : CommMonoid αᵒᵈ
  定义体: inferInstanceAs CommMonoid α

@[to_additive]

Depends on / 依赖: CommMonoid
-/
instance [CommMonoid α] : CommMonoid αᵒᵈ := inferInstanceAs CommMonoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LeftCancelMonoid
  signature: α] : LeftCancelMonoid αᵒᵈ
  body: inferInstanceAs LeftCancelMonoid α

@[to_additive]

中文:
实例 [LeftCancelMonoid
  签名: α] : LeftCancelMonoid αᵒᵈ
  定义体: inferInstanceAs LeftCancelMonoid α

@[to_additive]

Depends on / 依赖: LeftCancelMonoid
-/
instance [LeftCancelMonoid α] : LeftCancelMonoid αᵒᵈ := inferInstanceAs LeftCancelMonoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RightCancelMonoid
  signature: α] : RightCancelMonoid αᵒᵈ
  body: inferInstanceAs RightCancelMonoid α

@[to_additive]

中文:
实例 [RightCancelMonoid
  签名: α] : RightCancelMonoid αᵒᵈ
  定义体: inferInstanceAs RightCancelMonoid α

@[to_additive]

Depends on / 依赖: IsOrderedCancelMonoid, IsOrderedCancelMonoid.toMulLeftReflectLE, RightCancelMonoid, toMulLeftReflectLE
-/
instance [RightCancelMonoid α] : RightCancelMonoid αᵒᵈ := inferInstanceAs RightCancelMonoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CancelMonoid
  signature: α] : CancelMonoid αᵒᵈ
  body: inferInstanceAs CancelMonoid α

@[to_additive]

中文:
实例 [CancelMonoid
  签名: α] : CancelMonoid αᵒᵈ
  定义体: inferInstanceAs CancelMonoid α

@[to_additive]

Depends on / 依赖: CancelMonoid, IsOrderedCancelMonoid, IsOrderedCancelMonoid.toMulLeftReflectLT, MulLeftReflectLT, toMulLeftReflectLT
-/
instance [CancelMonoid α] : CancelMonoid αᵒᵈ := inferInstanceAs CancelMonoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CancelCommMonoid
  signature: α] : CancelCommMonoid αᵒᵈ
  body: inferInstanceAs CancelCommMonoid α

@[to_additive]

中文:
实例 [CancelCommMonoid
  签名: α] : CancelCommMonoid αᵒᵈ
  定义体: inferInstanceAs CancelCommMonoid α

@[to_additive]

Depends on / 依赖: CancelCommMonoid
-/
instance [CancelCommMonoid α] : CancelCommMonoid αᵒᵈ := inferInstanceAs CancelCommMonoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [InvolutiveInv
  signature: α] : InvolutiveInv αᵒᵈ
  body: inferInstanceAs InvolutiveInv α

@[to_additive]

中文:
实例 [InvolutiveInv
  签名: α] : InvolutiveInv αᵒᵈ
  定义体: inferInstanceAs InvolutiveInv α

@[to_additive]

Depends on / 依赖: InvolutiveInv, IsCancelMul, IsOrderedCancelMonoid, IsOrderedCancelMonoid.toIsCancelMul, toIsCancelMul
-/
instance [InvolutiveInv α] : InvolutiveInv αᵒᵈ := inferInstanceAs InvolutiveInv α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DivInvMonoid
  signature: α] : DivInvMonoid αᵒᵈ
  body: inferInstanceAs DivInvMonoid α

@[to_additive]

中文:
实例 [DivInvMonoid
  签名: α] : DivInvMonoid αᵒᵈ
  定义体: inferInstanceAs DivInvMonoid α

@[to_additive]

Depends on / 依赖: DivInvMonoid
-/
instance [DivInvMonoid α] : DivInvMonoid αᵒᵈ := inferInstanceAs DivInvMonoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DivisionMonoid
  signature: α] : DivisionMonoid αᵒᵈ
  body: inferInstanceAs DivisionMonoid α

@[to_additive]

中文:
实例 [DivisionMonoid
  签名: α] : DivisionMonoid αᵒᵈ
  定义体: inferInstanceAs DivisionMonoid α

@[to_additive]

Depends on / 依赖: DivisionMonoid
-/
instance [DivisionMonoid α] : DivisionMonoid αᵒᵈ := inferInstanceAs DivisionMonoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DivisionCommMonoid
  signature: α] : DivisionCommMonoid αᵒᵈ
  body: inferInstanceAs DivisionCommMonoid α

@[to_additive]

中文:
实例 [DivisionCommMonoid
  签名: α] : DivisionCommMonoid αᵒᵈ
  定义体: inferInstanceAs DivisionCommMonoid α

@[to_additive]

Depends on / 依赖: DivisionCommMonoid
-/
instance [DivisionCommMonoid α] : DivisionCommMonoid αᵒᵈ :=
inferInstanceAs DivisionCommMonoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Group
  signature: α] : Group αᵒᵈ
  body: inferInstanceAs Group α

@[to_additive]

中文:
实例 [Group
  签名: α] : Group αᵒᵈ
  定义体: inferInstanceAs Group α

@[to_additive]
-/
instance [Group α] : Group αᵒᵈ := inferInstanceAs Group α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommGroup
  signature: α] : CommGroup αᵒᵈ
  body: inferInstanceAs CommGroup α

中文:
实例 [CommGroup
  签名: α] : CommGroup αᵒᵈ
  定义体: inferInstanceAs CommGroup α

Depends on / 依赖: CommGroup
-/
instance [CommGroup α] : CommGroup αᵒᵈ := inferInstanceAs CommGroup α

end OrderDual

@[to_additive (attr := simp)]
/--
theorem `toDual_one` / 定理 `toDual_one`

English:
theorem toDual_one
  given: [One α]
  statement: toDual (1 : α) = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toDual_one
  条件: [One α]
  结论: toDual (1 : α) = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem toDual_one [One α] : toDual (1 : α) = 1 := rfl

@[to_additive (attr := simp)]
/--
theorem `ofDual_one` / 定理 `ofDual_one`

English:
theorem ofDual_one
  given: [One α]
  statement: (ofDual 1 : α) = 1
  proof: rfl

中文:
定理 ofDual_one
  条件: [One α]
  结论: (ofDual 1 : α) = 1
  证明: rfl
-/
theorem ofDual_one [One α] : (ofDual 1 : α) = 1 := rfl

/--
lemma `toDual_eq_one` / 引理 `toDual_eq_one`

English:
lemma toDual_eq_one
  given: [One α] {a : α}
  statement: toDual a = 1 ↔ a = 1
  proof: .rfl

中文:
引理 toDual_eq_one
  条件: [One α] {a : α}
  结论: toDual a = 1 ↔ a = 1
  证明: .rfl
-/
@[to_additive (attr := simp)] lemma toDual_eq_one [One α] {a : α} : toDual a = 1 ↔ a = 1 := .rfl
/--
lemma `ofDual_eq_one` / 引理 `ofDual_eq_one`

English:
lemma ofDual_eq_one
  given: [One α] {a : αᵒᵈ}
  statement: ofDual a = 1 ↔ a = 1
  proof: .rfl

@[to_additive (attr := simp)]

中文:
引理 ofDual_eq_one
  条件: [One α] {a : αᵒᵈ}
  结论: ofDual a = 1 ↔ a = 1
  证明: .rfl

@[to_additive (attr := simp)]
-/
@[to_additive (attr := simp)] lemma ofDual_eq_one [One α] {a : αᵒᵈ} : ofDual a = 1 ↔ a = 1 := .rfl

@[to_additive (attr := simp)]
/--
theorem `toDual_mul` / 定理 `toDual_mul`

English:
theorem toDual_mul
  given: [Mul α] (a b : α)
  statement: toDual (a * b) = toDual a * toDual b
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toDual_mul
  条件: [Mul α] (a b : α)
  结论: toDual (a * b) = toDual a * toDual b
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem toDual_mul [Mul α] (a b : α) : toDual (a * b) = toDual a * toDual b := rfl

@[to_additive (attr := simp)]
/--
theorem `ofDual_mul` / 定理 `ofDual_mul`

English:
theorem ofDual_mul
  given: [Mul α] (a b : αᵒᵈ)
  statement: ofDual (a * b) = ofDual a * ofDual b
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 ofDual_mul
  条件: [Mul α] (a b : αᵒᵈ)
  结论: ofDual (a * b) = ofDual a * ofDual b
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem ofDual_mul [Mul α] (a b : αᵒᵈ) : ofDual (a * b) = ofDual a * ofDual b := rfl

@[to_additive (attr := simp)]
/--
theorem `toDual_inv` / 定理 `toDual_inv`

English:
theorem toDual_inv
  given: [Inv α] (a : α)
  statement: toDual a⁻¹ = (toDual a)⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toDual_inv
  条件: [Inv α] (a : α)
  结论: toDual a⁻¹ = (toDual a)⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem toDual_inv [Inv α] (a : α) : toDual a⁻¹ = (toDual a)⁻¹ := rfl

@[to_additive (attr := simp)]
/--
theorem `ofDual_inv` / 定理 `ofDual_inv`

English:
theorem ofDual_inv
  given: [Inv α] (a : αᵒᵈ)
  statement: ofDual a⁻¹ = (ofDual a)⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 ofDual_inv
  条件: [Inv α] (a : αᵒᵈ)
  结论: ofDual a⁻¹ = (ofDual a)⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem ofDual_inv [Inv α] (a : αᵒᵈ) : ofDual a⁻¹ = (ofDual a)⁻¹ := rfl

@[to_additive (attr := simp)]
/--
theorem `toDual_div` / 定理 `toDual_div`

English:
theorem toDual_div
  given: [Div α] (a b : α)
  statement: toDual (a / b) = toDual a / toDual b
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toDual_div
  条件: [Div α] (a b : α)
  结论: toDual (a / b) = toDual a / toDual b
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem toDual_div [Div α] (a b : α) : toDual (a / b) = toDual a / toDual b := rfl

@[to_additive (attr := simp)]
/--
theorem `ofDual_div` / 定理 `ofDual_div`

English:
theorem ofDual_div
  given: [Div α] (a b : αᵒᵈ)
  statement: ofDual (a / b) = ofDual a / ofDual b
  proof: rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toDual_smul]

中文:
定理 ofDual_div
  条件: [Div α] (a b : αᵒᵈ)
  结论: ofDual (a / b) = ofDual a / ofDual b
  证明: rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toDual_smul]
-/
theorem ofDual_div [Div α] (a b : αᵒᵈ) : ofDual (a / b) = ofDual a / ofDual b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toDual_smul]
/--
theorem `toDual_pow` / 定理 `toDual_pow`

English:
theorem toDual_pow
  given: [Pow α β] (a : α) (b : β)
  statement: toDual (a ^ b) = toDual a ^ b
  proof: rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofDual_smul]

中文:
定理 toDual_pow
  条件: [Pow α β] (a : α) (b : β)
  结论: toDual (a ^ b) = toDual a ^ b
  证明: rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofDual_smul]
-/
theorem toDual_pow [Pow α β] (a : α) (b : β) : toDual (a ^ b) = toDual a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofDual_smul]
/--
theorem `ofDual_pow` / 定理 `ofDual_pow`

English:
theorem ofDual_pow
  given: [Pow α β] (a : αᵒᵈ) (b : β)
  statement: ofDual (a ^ b) = ofDual a ^ b
  proof: rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toDual_smul']

中文:
定理 ofDual_pow
  条件: [Pow α β] (a : αᵒᵈ) (b : β)
  结论: ofDual (a ^ b) = ofDual a ^ b
  证明: rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toDual_smul']
-/
theorem ofDual_pow [Pow α β] (a : αᵒᵈ) (b : β) : ofDual (a ^ b) = ofDual a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toDual_smul']
/--
theorem `pow_toDual` / 定理 `pow_toDual`

English:
theorem pow_toDual
  given: [Pow α β] (a : α) (b : β)
  statement: a ^ toDual b = a ^ b
  proof: rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofDual_smul']

中文:
定理 pow_toDual
  条件: [Pow α β] (a : α) (b : β)
  结论: a ^ toDual b = a ^ b
  证明: rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofDual_smul']
-/
theorem pow_toDual [Pow α β] (a : α) (b : β) : a ^ toDual b = a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofDual_smul']
/--
theorem `pow_ofDual` / 定理 `pow_ofDual`

English:
theorem pow_ofDual
  given: [Pow α β] (a : α) (b : βᵒᵈ)
  statement: a ^ ofDual b = a ^ b
  proof: rfl

中文:
定理 pow_ofDual
  条件: [Pow α β] (a : α) (b : βᵒᵈ)
  结论: a ^ ofDual b = a ^ b
  证明: rfl
-/
theorem pow_ofDual [Pow α β] (a : α) (b : βᵒᵈ) : a ^ ofDual b = a ^ b := rfl

section Monoid
variable [Monoid α]

@[to_additive (attr := simp)]
/--
lemma `isLeftRegular_toDual` / 引理 `isLeftRegular_toDual`

English:
lemma isLeftRegular_toDual
  given: {a : α}
  statement: IsLeftRegular (toDual a) ↔ IsLeftRegular a
  proof: .rfl

@[to_additive (attr := simp)]

中文:
引理 isLeftRegular_toDual
  条件: {a : α}
  结论: IsLeftRegular (toDual a) ↔ IsLeftRegular a
  证明: .rfl

@[to_additive (attr := simp)]
-/
lemma isLeftRegular_toDual {a : α} : IsLeftRegular (toDual a) ↔ IsLeftRegular a := .rfl

@[to_additive (attr := simp)]
/--
lemma `isLeftRegular_ofDual` / 引理 `isLeftRegular_ofDual`

English:
lemma isLeftRegular_ofDual
  given: {a : αᵒᵈ}
  statement: IsLeftRegular (ofDual a) ↔ IsLeftRegular a
  proof: .rfl

@[to_additive (attr := simp)]

中文:
引理 isLeftRegular_ofDual
  条件: {a : αᵒᵈ}
  结论: IsLeftRegular (ofDual a) ↔ IsLeftRegular a
  证明: .rfl

@[to_additive (attr := simp)]
-/
lemma isLeftRegular_ofDual {a : αᵒᵈ} : IsLeftRegular (ofDual a) ↔ IsLeftRegular a := .rfl

@[to_additive (attr := simp)]
/--
lemma `isRightRegular_toDual` / 引理 `isRightRegular_toDual`

English:
lemma isRightRegular_toDual
  given: {a : α}
  statement: IsRightRegular (toDual a) ↔ IsRightRegular a
  proof: .rfl

@[to_additive (attr := simp)]

中文:
引理 isRightRegular_toDual
  条件: {a : α}
  结论: IsRightRegular (toDual a) ↔ IsRightRegular a
  证明: .rfl

@[to_additive (attr := simp)]
-/
lemma isRightRegular_toDual {a : α} : IsRightRegular (toDual a) ↔ IsRightRegular a := .rfl

@[to_additive (attr := simp)]
/--
lemma `isRightRegular_ofDual` / 引理 `isRightRegular_ofDual`

English:
lemma isRightRegular_ofDual
  given: {a : αᵒᵈ}
  statement: IsRightRegular (ofDual a) ↔ IsRightRegular a
  proof: .rfl

@[to_additive (attr := simp)]

中文:
引理 isRightRegular_ofDual
  条件: {a : αᵒᵈ}
  结论: IsRightRegular (ofDual a) ↔ IsRightRegular a
  证明: .rfl

@[to_additive (attr := simp)]
-/
lemma isRightRegular_ofDual {a : αᵒᵈ} : IsRightRegular (ofDual a) ↔ IsRightRegular a := .rfl

@[to_additive (attr := simp)]
/--
lemma `isRegular_toDual` / 引理 `isRegular_toDual`

English:
lemma isRegular_toDual
  given: {a : α}
  statement: IsRegular (toDual a) ↔ IsRegular a
  proof: .rfl

@[to_additive (attr := simp)]

中文:
引理 isRegular_toDual
  条件: {a : α}
  结论: IsRegular (toDual a) ↔ IsRegular a
  证明: .rfl

@[to_additive (attr := simp)]
-/
lemma isRegular_toDual {a : α} : IsRegular (toDual a) ↔ IsRegular a := .rfl

@[to_additive (attr := simp)]
/--
lemma `isRegular_ofDual` / 引理 `isRegular_ofDual`

English:
lemma isRegular_ofDual
  given: {a : αᵒᵈ}
  statement: IsRegular (ofDual a) ↔ IsRegular a
  proof: .rfl

中文:
引理 isRegular_ofDual
  条件: {a : αᵒᵈ}
  结论: IsRegular (ofDual a) ↔ IsRegular a
  证明: .rfl
-/
lemma isRegular_ofDual {a : αᵒᵈ} : IsRegular (ofDual a) ↔ IsRegular a := .rfl

end Monoid

/-! ### Lexicographical order -/


namespace Lex

set_option backward.inferInstanceAs.wrap.instances false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [One
  signature: α] : One (Lex α)
  body: inferInstanceAs One α

中文:
实例 [One
  签名: α] : One (Lex α)
  定义体: inferInstanceAs One α
-/
@[to_additive] instance [One α] : One (Lex α) := inferInstanceAs One α

set_option backward.inferInstanceAs.wrap.instances false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] : Mul (Lex α)
  body: inferInstanceAs Mul α

中文:
实例 [Mul
  签名: α] : Mul (Lex α)
  定义体: inferInstanceAs Mul α
-/
@[to_additive] instance [Mul α] : Mul (Lex α) := inferInstanceAs Mul α

set_option backward.inferInstanceAs.wrap.instances false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inv
  signature: α] : Inv (Lex α)
  body: inferInstanceAs Inv α

中文:
实例 [Inv
  签名: α] : Inv (Lex α)
  定义体: inferInstanceAs Inv α
-/
@[to_additive] instance [Inv α] : Inv (Lex α) := inferInstanceAs Inv α

set_option backward.inferInstanceAs.wrap.instances false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Div
  signature: α] : Div (Lex α)
  body: inferInstanceAs Div α

中文:
实例 [Div
  签名: α] : Div (Lex α)
  定义体: inferInstanceAs Div α
-/
@[to_additive] instance [Div α] : Div (Lex α) := inferInstanceAs Div α

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive (attr := to_additive) (reorder := 1 2) instSMul]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Pow
  signature: α β] : Pow (Lex α) β
  body: inferInstanceAs Pow α β

中文:
实例 [Pow
  签名: α β] : Pow (Lex α) β
  定义体: inferInstanceAs Pow α β
-/
instance [Pow α β] : Pow (Lex α) β := inferInstanceAs Pow α β

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive (attr := to_additive) (reorder := 1 2) instSMul']
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Pow
  signature: α β] : Pow α (Lex β)
  body: inferInstanceAs Pow α β

@[to_additive]

中文:
实例 [Pow
  签名: α β] : Pow α (Lex β)
  定义体: inferInstanceAs Pow α β

@[to_additive]
-/
instance [Pow α β] : Pow α (Lex β) := inferInstanceAs Pow α β

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semigroup
  signature: α] : Semigroup (Lex α)
  body: inferInstanceAs Semigroup α

@[to_additive]

中文:
实例 [Semigroup
  签名: α] : Semigroup (Lex α)
  定义体: inferInstanceAs Semigroup α

@[to_additive]

Depends on / 依赖: Semigroup
-/
instance [Semigroup α] : Semigroup (Lex α) := inferInstanceAs Semigroup α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemigroup
  signature: α] : CommSemigroup (Lex α)
  body: inferInstanceAs CommSemigroup α

@[to_additive]

中文:
实例 [CommSemigroup
  签名: α] : CommSemigroup (Lex α)
  定义体: inferInstanceAs CommSemigroup α

@[to_additive]

Depends on / 依赖: CommSemigroup
-/
instance [CommSemigroup α] : CommSemigroup (Lex α) := inferInstanceAs CommSemigroup α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [IsLeftCancelMul α] : IsLeftCancelMul (Lex α)
  body: inferInstanceAs IsLeftCancelMul α

@[to_additive]

中文:
实例 [Mul
  签名: α] [IsLeftCancelMul α] : IsLeftCancelMul (Lex α)
  定义体: inferInstanceAs IsLeftCancelMul α

@[to_additive]

Depends on / 依赖: IsLeftCancelMul
-/
instance [Mul α] [IsLeftCancelMul α] : IsLeftCancelMul (Lex α) :=
inferInstanceAs IsLeftCancelMul α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [IsRightCancelMul α] : IsRightCancelMul (Lex α)
  body: inferInstanceAs IsRightCancelMul α

@[to_additive]

中文:
实例 [Mul
  签名: α] [IsRightCancelMul α] : IsRightCancelMul (Lex α)
  定义体: inferInstanceAs IsRightCancelMul α

@[to_additive]

Depends on / 依赖: IsRightCancelMul
-/
instance [Mul α] [IsRightCancelMul α] : IsRightCancelMul (Lex α) :=
inferInstanceAs IsRightCancelMul α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [IsCancelMul α] : IsCancelMul (Lex α)
  body: inferInstanceAs IsCancelMul α

@[to_additive]

中文:
实例 [Mul
  签名: α] [IsCancelMul α] : IsCancelMul (Lex α)
  定义体: inferInstanceAs IsCancelMul α

@[to_additive]

Depends on / 依赖: IsCancelMul
-/
instance [Mul α] [IsCancelMul α] : IsCancelMul (Lex α) :=
inferInstanceAs IsCancelMul α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LeftCancelSemigroup
  signature: α] : LeftCancelSemigroup (Lex α)
  body: inferInstanceAs LeftCancelSemigroup α

@[to_additive]

中文:
实例 [LeftCancelSemigroup
  签名: α] : LeftCancelSemigroup (Lex α)
  定义体: inferInstanceAs LeftCancelSemigroup α

@[to_additive]

Depends on / 依赖: LeftCancelSemigroup
-/
instance [LeftCancelSemigroup α] : LeftCancelSemigroup (Lex α) :=
inferInstanceAs LeftCancelSemigroup α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RightCancelSemigroup
  signature: α] : RightCancelSemigroup (Lex α)
  body: inferInstanceAs RightCancelSemigroup α

@[to_additive]

中文:
实例 [RightCancelSemigroup
  签名: α] : RightCancelSemigroup (Lex α)
  定义体: inferInstanceAs RightCancelSemigroup α

@[to_additive]

Depends on / 依赖: RightCancelSemigroup
-/
instance [RightCancelSemigroup α] : RightCancelSemigroup (Lex α) :=
inferInstanceAs RightCancelSemigroup α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulOneClass
  signature: α] : MulOneClass (Lex α)
  body: inferInstanceAs MulOneClass α

@[to_additive]

中文:
实例 [MulOneClass
  签名: α] : MulOneClass (Lex α)
  定义体: inferInstanceAs MulOneClass α

@[to_additive]

Depends on / 依赖: MulOneClass
-/
instance [MulOneClass α] : MulOneClass (Lex α) := inferInstanceAs MulOneClass α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: α] : Monoid (Lex α)
  body: inferInstanceAs Monoid α

@[to_additive]

中文:
实例 [Monoid
  签名: α] : Monoid (Lex α)
  定义体: inferInstanceAs Monoid α

@[to_additive]

Depends on / 依赖: Monoid
-/
instance [Monoid α] : Monoid (Lex α) := inferInstanceAs Monoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommMonoid
  signature: α] : CommMonoid (Lex α)
  body: inferInstanceAs CommMonoid α

@[to_additive]

中文:
实例 [CommMonoid
  签名: α] : CommMonoid (Lex α)
  定义体: inferInstanceAs CommMonoid α

@[to_additive]

Depends on / 依赖: CommMonoid
-/
instance [CommMonoid α] : CommMonoid (Lex α) := inferInstanceAs CommMonoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LeftCancelMonoid
  signature: α] : LeftCancelMonoid (Lex α)
  body: inferInstanceAs LeftCancelMonoid α

@[to_additive]

中文:
实例 [LeftCancelMonoid
  签名: α] : LeftCancelMonoid (Lex α)
  定义体: inferInstanceAs LeftCancelMonoid α

@[to_additive]

Depends on / 依赖: LeftCancelMonoid
-/
instance [LeftCancelMonoid α] : LeftCancelMonoid (Lex α) := inferInstanceAs LeftCancelMonoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RightCancelMonoid
  signature: α] : RightCancelMonoid (Lex α)
  body: inferInstanceAs RightCancelMonoid α

@[to_additive]

中文:
实例 [RightCancelMonoid
  签名: α] : RightCancelMonoid (Lex α)
  定义体: inferInstanceAs RightCancelMonoid α

@[to_additive]

Depends on / 依赖: RightCancelMonoid
-/
instance [RightCancelMonoid α] : RightCancelMonoid (Lex α) := inferInstanceAs RightCancelMonoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CancelMonoid
  signature: α] : CancelMonoid (Lex α)
  body: inferInstanceAs CancelMonoid α

@[to_additive]

中文:
实例 [CancelMonoid
  签名: α] : CancelMonoid (Lex α)
  定义体: inferInstanceAs CancelMonoid α

@[to_additive]

Depends on / 依赖: CancelMonoid
-/
instance [CancelMonoid α] : CancelMonoid (Lex α) := inferInstanceAs CancelMonoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CancelCommMonoid
  signature: α] : CancelCommMonoid (Lex α)
  body: inferInstanceAs CancelCommMonoid α

@[to_additive]

中文:
实例 [CancelCommMonoid
  签名: α] : CancelCommMonoid (Lex α)
  定义体: inferInstanceAs CancelCommMonoid α

@[to_additive]

Depends on / 依赖: CancelCommMonoid
-/
instance [CancelCommMonoid α] : CancelCommMonoid (Lex α) := inferInstanceAs CancelCommMonoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [InvolutiveInv
  signature: α] : InvolutiveInv (Lex α)
  body: inferInstanceAs InvolutiveInv α

@[to_additive]

中文:
实例 [InvolutiveInv
  签名: α] : InvolutiveInv (Lex α)
  定义体: inferInstanceAs InvolutiveInv α

@[to_additive]

Depends on / 依赖: InvolutiveInv
-/
instance [InvolutiveInv α] : InvolutiveInv (Lex α) := inferInstanceAs InvolutiveInv α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DivInvMonoid
  signature: α] : DivInvMonoid (Lex α)
  body: inferInstanceAs DivInvMonoid α

@[to_additive]

中文:
实例 [DivInvMonoid
  签名: α] : DivInvMonoid (Lex α)
  定义体: inferInstanceAs DivInvMonoid α

@[to_additive]

Depends on / 依赖: DivInvMonoid
-/
instance [DivInvMonoid α] : DivInvMonoid (Lex α) := inferInstanceAs DivInvMonoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DivisionMonoid
  signature: α] : DivisionMonoid (Lex α)
  body: inferInstanceAs DivisionMonoid α

@[to_additive]

中文:
实例 [DivisionMonoid
  签名: α] : DivisionMonoid (Lex α)
  定义体: inferInstanceAs DivisionMonoid α

@[to_additive]

Depends on / 依赖: DivisionMonoid
-/
instance [DivisionMonoid α] : DivisionMonoid (Lex α) := inferInstanceAs DivisionMonoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DivisionCommMonoid
  signature: α] : DivisionCommMonoid (Lex α)
  body: inferInstanceAs DivisionCommMonoid α

@[to_additive]

中文:
实例 [DivisionCommMonoid
  签名: α] : DivisionCommMonoid (Lex α)
  定义体: inferInstanceAs DivisionCommMonoid α

@[to_additive]

Depends on / 依赖: DivisionCommMonoid
-/
instance [DivisionCommMonoid α] : DivisionCommMonoid (Lex α) :=
inferInstanceAs DivisionCommMonoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Group
  signature: α] : Group (Lex α)
  body: inferInstanceAs Group α

@[to_additive]

中文:
实例 [Group
  签名: α] : Group (Lex α)
  定义体: inferInstanceAs Group α

@[to_additive]
-/
instance [Group α] : Group (Lex α) := inferInstanceAs Group α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommGroup
  signature: α] : CommGroup (Lex α)
  body: inferInstanceAs CommGroup α

中文:
实例 [CommGroup
  签名: α] : CommGroup (Lex α)
  定义体: inferInstanceAs CommGroup α

Depends on / 依赖: CommGroup
-/
instance [CommGroup α] : CommGroup (Lex α) := inferInstanceAs CommGroup α

end Lex

@[to_additive (attr := simp)]
/--
theorem `toLex_one` / 定理 `toLex_one`

English:
theorem toLex_one
  given: [One α]
  statement: toLex (1 : α) = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toLex_one
  条件: [One α]
  结论: toLex (1 : α) = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem toLex_one [One α] : toLex (1 : α) = 1 := rfl

@[to_additive (attr := simp)]
/--
theorem `toLex_eq_one` / 定理 `toLex_eq_one`

English:
theorem toLex_eq_one
  given: [One α] {a : α}
  statement: toLex a = 1 ↔ a = 1
  proof: .rfl

@[to_additive (attr := simp)]

中文:
定理 toLex_eq_one
  条件: [One α] {a : α}
  结论: toLex a = 1 ↔ a = 1
  证明: .rfl

@[to_additive (attr := simp)]
-/
theorem toLex_eq_one [One α] {a : α} : toLex a = 1 ↔ a = 1 := .rfl

@[to_additive (attr := simp)]
/--
theorem `ofLex_one` / 定理 `ofLex_one`

English:
theorem ofLex_one
  given: [One α]
  statement: (ofLex 1 : α) = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 ofLex_one
  条件: [One α]
  结论: (ofLex 1 : α) = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem ofLex_one [One α] : (ofLex 1 : α) = 1 := rfl

@[to_additive (attr := simp)]
/--
theorem `ofLex_eq_one` / 定理 `ofLex_eq_one`

English:
theorem ofLex_eq_one
  given: [One α] {a : Lex α}
  statement: ofLex a = 1 ↔ a = 1
  proof: .rfl

@[to_additive (attr := simp)]

中文:
定理 ofLex_eq_one
  条件: [One α] {a : Lex α}
  结论: ofLex a = 1 ↔ a = 1
  证明: .rfl

@[to_additive (attr := simp)]
-/
theorem ofLex_eq_one [One α] {a : Lex α} : ofLex a = 1 ↔ a = 1 := .rfl

@[to_additive (attr := simp)]
/--
theorem `toLex_mul` / 定理 `toLex_mul`

English:
theorem toLex_mul
  given: [Mul α] (a b : α)
  statement: toLex (a * b) = toLex a * toLex b
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toLex_mul
  条件: [Mul α] (a b : α)
  结论: toLex (a * b) = toLex a * toLex b
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem toLex_mul [Mul α] (a b : α) : toLex (a * b) = toLex a * toLex b := rfl

@[to_additive (attr := simp)]
/--
theorem `ofLex_mul` / 定理 `ofLex_mul`

English:
theorem ofLex_mul
  given: [Mul α] (a b : Lex α)
  statement: ofLex (a * b) = ofLex a * ofLex b
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 ofLex_mul
  条件: [Mul α] (a b : Lex α)
  结论: ofLex (a * b) = ofLex a * ofLex b
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem ofLex_mul [Mul α] (a b : Lex α) : ofLex (a * b) = ofLex a * ofLex b := rfl

@[to_additive (attr := simp)]
/--
theorem `toLex_inv` / 定理 `toLex_inv`

English:
theorem toLex_inv
  given: [Inv α] (a : α)
  statement: toLex a⁻¹ = (toLex a)⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toLex_inv
  条件: [Inv α] (a : α)
  结论: toLex a⁻¹ = (toLex a)⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem toLex_inv [Inv α] (a : α) : toLex a⁻¹ = (toLex a)⁻¹ := rfl

@[to_additive (attr := simp)]
/--
theorem `ofLex_inv` / 定理 `ofLex_inv`

English:
theorem ofLex_inv
  given: [Inv α] (a : Lex α)
  statement: ofLex a⁻¹ = (ofLex a)⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 ofLex_inv
  条件: [Inv α] (a : Lex α)
  结论: ofLex a⁻¹ = (ofLex a)⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem ofLex_inv [Inv α] (a : Lex α) : ofLex a⁻¹ = (ofLex a)⁻¹ := rfl

@[to_additive (attr := simp)]
/--
theorem `toLex_div` / 定理 `toLex_div`

English:
theorem toLex_div
  given: [Div α] (a b : α)
  statement: toLex (a / b) = toLex a / toLex b
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toLex_div
  条件: [Div α] (a b : α)
  结论: toLex (a / b) = toLex a / toLex b
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem toLex_div [Div α] (a b : α) : toLex (a / b) = toLex a / toLex b := rfl

@[to_additive (attr := simp)]
/--
theorem `ofLex_div` / 定理 `ofLex_div`

English:
theorem ofLex_div
  given: [Div α] (a b : Lex α)
  statement: ofLex (a / b) = ofLex a / ofLex b
  proof: rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toLex_smul]

中文:
定理 ofLex_div
  条件: [Div α] (a b : Lex α)
  结论: ofLex (a / b) = ofLex a / ofLex b
  证明: rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toLex_smul]
-/
theorem ofLex_div [Div α] (a b : Lex α) : ofLex (a / b) = ofLex a / ofLex b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toLex_smul]
/--
theorem `toLex_pow` / 定理 `toLex_pow`

English:
theorem toLex_pow
  given: [Pow α β] (a : α) (b : β)
  statement: toLex (a ^ b) = toLex a ^ b
  proof: rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofLex_smul]

中文:
定理 toLex_pow
  条件: [Pow α β] (a : α) (b : β)
  结论: toLex (a ^ b) = toLex a ^ b
  证明: rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofLex_smul]
-/
theorem toLex_pow [Pow α β] (a : α) (b : β) : toLex (a ^ b) = toLex a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofLex_smul]
/--
theorem `ofLex_pow` / 定理 `ofLex_pow`

English:
theorem ofLex_pow
  given: [Pow α β] (a : Lex α) (b : β)
  statement: ofLex (a ^ b) = ofLex a ^ b
  proof: rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toLex_smul']

中文:
定理 ofLex_pow
  条件: [Pow α β] (a : Lex α) (b : β)
  结论: ofLex (a ^ b) = ofLex a ^ b
  证明: rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toLex_smul']
-/
theorem ofLex_pow [Pow α β] (a : Lex α) (b : β) : ofLex (a ^ b) = ofLex a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toLex_smul']
/--
theorem `pow_toLex` / 定理 `pow_toLex`

English:
theorem pow_toLex
  given: [Pow α β] (a : α) (b : β)
  statement: a ^ toLex b = a ^ b
  proof: rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofLex_smul']

中文:
定理 pow_toLex
  条件: [Pow α β] (a : α) (b : β)
  结论: a ^ toLex b = a ^ b
  证明: rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofLex_smul']
-/
theorem pow_toLex [Pow α β] (a : α) (b : β) : a ^ toLex b = a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofLex_smul']
/--
theorem `pow_ofLex` / 定理 `pow_ofLex`

English:
theorem pow_ofLex
  given: [Pow α β] (a : α) (b : Lex β)
  statement: a ^ ofLex b = a ^ b
  proof: rfl

中文:
定理 pow_ofLex
  条件: [Pow α β] (a : α) (b : Lex β)
  结论: a ^ ofLex b = a ^ b
  证明: rfl
-/
theorem pow_ofLex [Pow α β] (a : α) (b : Lex β) : a ^ ofLex b = a ^ b := rfl

section Monoid
variable [Monoid α]

@[to_additive (attr := simp)]
/--
lemma `isLeftRegular_toLex` / 引理 `isLeftRegular_toLex`

English:
lemma isLeftRegular_toLex
  given: {a : α}
  statement: IsLeftRegular (toLex a) ↔ IsLeftRegular a
  proof: .rfl

@[to_additive (attr := simp)]

中文:
引理 isLeftRegular_toLex
  条件: {a : α}
  结论: IsLeftRegular (toLex a) ↔ IsLeftRegular a
  证明: .rfl

@[to_additive (attr := simp)]
-/
lemma isLeftRegular_toLex {a : α} : IsLeftRegular (toLex a) ↔ IsLeftRegular a := .rfl

@[to_additive (attr := simp)]
/--
lemma `isLeftRegular_ofLex` / 引理 `isLeftRegular_ofLex`

English:
lemma isLeftRegular_ofLex
  given: {a : Lex α}
  statement: IsLeftRegular (ofLex a) ↔ IsLeftRegular a
  proof: .rfl

@[to_additive (attr := simp)]

中文:
引理 isLeftRegular_ofLex
  条件: {a : Lex α}
  结论: IsLeftRegular (ofLex a) ↔ IsLeftRegular a
  证明: .rfl

@[to_additive (attr := simp)]

Depends on / 依赖: CommMonoid, IsOrderedMonoid, Preorder, toIsOrderedMonoid
-/
lemma isLeftRegular_ofLex {a : Lex α} : IsLeftRegular (ofLex a) ↔ IsLeftRegular a := .rfl

@[to_additive (attr := simp)]
/--
lemma `isRightRegular_toLex` / 引理 `isRightRegular_toLex`

English:
lemma isRightRegular_toLex
  given: {a : α}
  statement: IsRightRegular (toLex a) ↔ IsRightRegular a
  proof: .rfl

@[to_additive (attr := simp)]

中文:
引理 isRightRegular_toLex
  条件: {a : α}
  结论: IsRightRegular (toLex a) ↔ IsRightRegular a
  证明: .rfl

@[to_additive (attr := simp)]

Depends on / 依赖: toIsOrderedCancelMonoid
-/
lemma isRightRegular_toLex {a : α} : IsRightRegular (toLex a) ↔ IsRightRegular a := .rfl

@[to_additive (attr := simp)]
/--
lemma `isRightRegular_ofLex` / 引理 `isRightRegular_ofLex`

English:
lemma isRightRegular_ofLex
  given: {a : Lex α}
  statement: IsRightRegular (ofLex a) ↔ IsRightRegular a
  proof: .rfl

@[to_additive (attr := simp)]

中文:
引理 isRightRegular_ofLex
  条件: {a : Lex α}
  结论: IsRightRegular (ofLex a) ↔ IsRightRegular a
  证明: .rfl

@[to_additive (attr := simp)]
-/
lemma isRightRegular_ofLex {a : Lex α} : IsRightRegular (ofLex a) ↔ IsRightRegular a := .rfl

@[to_additive (attr := simp)]
/--
lemma `isRegular_toLex` / 引理 `isRegular_toLex`

English:
lemma isRegular_toLex
  given: {a : α}
  statement: IsRegular (toLex a) ↔ IsRegular a
  proof: .rfl

@[to_additive (attr := simp)]

中文:
引理 isRegular_toLex
  条件: {a : α}
  结论: IsRegular (toLex a) ↔ IsRegular a
  证明: .rfl

@[to_additive (attr := simp)]
-/
lemma isRegular_toLex {a : α} : IsRegular (toLex a) ↔ IsRegular a := .rfl

@[to_additive (attr := simp)]
/--
lemma `isRegular_ofLex` / 引理 `isRegular_ofLex`

English:
lemma isRegular_ofLex
  given: {a : Lex α}
  statement: IsRegular (ofLex a) ↔ IsRegular a
  proof: .rfl

中文:
引理 isRegular_ofLex
  条件: {a : Lex α}
  结论: IsRegular (ofLex a) ↔ IsRegular a
  证明: .rfl
-/
lemma isRegular_ofLex {a : Lex α} : IsRegular (ofLex a) ↔ IsRegular a := .rfl

end Monoid

/-! ### Colexicographical order -/


namespace Colex

set_option backward.inferInstanceAs.wrap.instances false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [One
  signature: α] : One (Colex α)
  body: inferInstanceAs One α

中文:
实例 [One
  签名: α] : One (Colex α)
  定义体: inferInstanceAs One α
-/
@[to_additive] instance [One α] : One (Colex α) := inferInstanceAs One α

set_option backward.inferInstanceAs.wrap.instances false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] : Mul (Colex α)
  body: inferInstanceAs Mul α

中文:
实例 [Mul
  签名: α] : Mul (Colex α)
  定义体: inferInstanceAs Mul α
-/
@[to_additive] instance [Mul α] : Mul (Colex α) := inferInstanceAs Mul α

set_option backward.inferInstanceAs.wrap.instances false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inv
  signature: α] : Inv (Colex α)
  body: inferInstanceAs Inv α

中文:
实例 [Inv
  签名: α] : Inv (Colex α)
  定义体: inferInstanceAs Inv α
-/
@[to_additive] instance [Inv α] : Inv (Colex α) := inferInstanceAs Inv α

set_option backward.inferInstanceAs.wrap.instances false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Div
  signature: α] : Div (Colex α)
  body: inferInstanceAs Div α

中文:
实例 [Div
  签名: α] : Div (Colex α)
  定义体: inferInstanceAs Div α
-/
@[to_additive] instance [Div α] : Div (Colex α) := inferInstanceAs Div α

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive (attr := to_additive) (reorder := 1 2) instSMul]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Pow
  signature: α β] : Pow (Colex α) β
  body: inferInstanceAs Pow α β

中文:
实例 [Pow
  签名: α β] : Pow (Colex α) β
  定义体: inferInstanceAs Pow α β
-/
instance [Pow α β] : Pow (Colex α) β := inferInstanceAs Pow α β

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive (attr := to_additive) (reorder := 1 2) instSMul']
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Pow
  signature: α β] : Pow α (Colex β)
  body: inferInstanceAs Pow α β

@[to_additive]

中文:
实例 [Pow
  签名: α β] : Pow α (Colex β)
  定义体: inferInstanceAs Pow α β

@[to_additive]
-/
instance [Pow α β] : Pow α (Colex β) := inferInstanceAs Pow α β

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semigroup
  signature: α] : Semigroup (Colex α)
  body: inferInstanceAs Semigroup α

@[to_additive]

中文:
实例 [Semigroup
  签名: α] : Semigroup (Colex α)
  定义体: inferInstanceAs Semigroup α

@[to_additive]

Depends on / 依赖: Semigroup
-/
instance [Semigroup α] : Semigroup (Colex α) := inferInstanceAs Semigroup α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemigroup
  signature: α] : CommSemigroup (Colex α)
  body: inferInstanceAs CommSemigroup α

@[to_additive]

中文:
实例 [CommSemigroup
  签名: α] : CommSemigroup (Colex α)
  定义体: inferInstanceAs CommSemigroup α

@[to_additive]

Depends on / 依赖: CommSemigroup
-/
instance [CommSemigroup α] : CommSemigroup (Colex α) := inferInstanceAs CommSemigroup α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [IsLeftCancelMul α] : IsLeftCancelMul (Colex α)
  body: inferInstanceAs IsLeftCancelMul α

@[to_additive]

中文:
实例 [Mul
  签名: α] [IsLeftCancelMul α] : IsLeftCancelMul (Colex α)
  定义体: inferInstanceAs IsLeftCancelMul α

@[to_additive]

Depends on / 依赖: IsLeftCancelMul
-/
instance [Mul α] [IsLeftCancelMul α] : IsLeftCancelMul (Colex α) :=
inferInstanceAs IsLeftCancelMul α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [IsRightCancelMul α] : IsRightCancelMul (Colex α)
  body: inferInstanceAs IsRightCancelMul α

@[to_additive]

中文:
实例 [Mul
  签名: α] [IsRightCancelMul α] : IsRightCancelMul (Colex α)
  定义体: inferInstanceAs IsRightCancelMul α

@[to_additive]

Depends on / 依赖: IsRightCancelMul
-/
instance [Mul α] [IsRightCancelMul α] : IsRightCancelMul (Colex α) :=
inferInstanceAs IsRightCancelMul α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [IsCancelMul α] : IsCancelMul (Colex α)
  body: inferInstanceAs IsCancelMul α

@[to_additive]

中文:
实例 [Mul
  签名: α] [IsCancelMul α] : IsCancelMul (Colex α)
  定义体: inferInstanceAs IsCancelMul α

@[to_additive]

Depends on / 依赖: IsCancelMul
-/
instance [Mul α] [IsCancelMul α] : IsCancelMul (Colex α) :=
inferInstanceAs IsCancelMul α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LeftCancelSemigroup
  signature: α] : LeftCancelSemigroup (Colex α)
  body: inferInstanceAs LeftCancelSemigroup α

@[to_additive]

中文:
实例 [LeftCancelSemigroup
  签名: α] : LeftCancelSemigroup (Colex α)
  定义体: inferInstanceAs LeftCancelSemigroup α

@[to_additive]

Depends on / 依赖: LeftCancelSemigroup
-/
instance [LeftCancelSemigroup α] : LeftCancelSemigroup (Colex α) :=
inferInstanceAs LeftCancelSemigroup α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RightCancelSemigroup
  signature: α] : RightCancelSemigroup (Colex α)
  body: inferInstanceAs RightCancelSemigroup α

@[to_additive]

中文:
实例 [RightCancelSemigroup
  签名: α] : RightCancelSemigroup (Colex α)
  定义体: inferInstanceAs RightCancelSemigroup α

@[to_additive]

Depends on / 依赖: RightCancelSemigroup
-/
instance [RightCancelSemigroup α] : RightCancelSemigroup (Colex α) :=
inferInstanceAs RightCancelSemigroup α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulOneClass
  signature: α] : MulOneClass (Colex α)
  body: inferInstanceAs MulOneClass α

@[to_additive]

中文:
实例 [MulOneClass
  签名: α] : MulOneClass (Colex α)
  定义体: inferInstanceAs MulOneClass α

@[to_additive]

Depends on / 依赖: MulOneClass
-/
instance [MulOneClass α] : MulOneClass (Colex α) := inferInstanceAs MulOneClass α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: α] : Monoid (Colex α)
  body: inferInstanceAs Monoid α

@[to_additive]

中文:
实例 [Monoid
  签名: α] : Monoid (Colex α)
  定义体: inferInstanceAs Monoid α

@[to_additive]

Depends on / 依赖: Monoid
-/
instance [Monoid α] : Monoid (Colex α) := inferInstanceAs Monoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommMonoid
  signature: α] : CommMonoid (Colex α)
  body: inferInstanceAs CommMonoid α

@[to_additive]

中文:
实例 [CommMonoid
  签名: α] : CommMonoid (Colex α)
  定义体: inferInstanceAs CommMonoid α

@[to_additive]

Depends on / 依赖: CommMonoid
-/
instance [CommMonoid α] : CommMonoid (Colex α) := inferInstanceAs CommMonoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LeftCancelMonoid
  signature: α] : LeftCancelMonoid (Colex α)
  body: inferInstanceAs LeftCancelMonoid α

@[to_additive]

中文:
实例 [LeftCancelMonoid
  签名: α] : LeftCancelMonoid (Colex α)
  定义体: inferInstanceAs LeftCancelMonoid α

@[to_additive]

Depends on / 依赖: LeftCancelMonoid
-/
instance [LeftCancelMonoid α] : LeftCancelMonoid (Colex α) := inferInstanceAs LeftCancelMonoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RightCancelMonoid
  signature: α] : RightCancelMonoid (Colex α)
  body: inferInstanceAs RightCancelMonoid α

@[to_additive]

中文:
实例 [RightCancelMonoid
  签名: α] : RightCancelMonoid (Colex α)
  定义体: inferInstanceAs RightCancelMonoid α

@[to_additive]

Depends on / 依赖: RightCancelMonoid
-/
instance [RightCancelMonoid α] : RightCancelMonoid (Colex α) :=
inferInstanceAs RightCancelMonoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CancelMonoid
  signature: α] : CancelMonoid (Colex α)
  body: inferInstanceAs CancelMonoid α

@[to_additive]

中文:
实例 [CancelMonoid
  签名: α] : CancelMonoid (Colex α)
  定义体: inferInstanceAs CancelMonoid α

@[to_additive]

Depends on / 依赖: CancelMonoid
-/
instance [CancelMonoid α] : CancelMonoid (Colex α) := inferInstanceAs CancelMonoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CancelCommMonoid
  signature: α] : CancelCommMonoid (Colex α)
  body: inferInstanceAs CancelCommMonoid α

@[to_additive]

中文:
实例 [CancelCommMonoid
  签名: α] : CancelCommMonoid (Colex α)
  定义体: inferInstanceAs CancelCommMonoid α

@[to_additive]

Depends on / 依赖: CancelCommMonoid
-/
instance [CancelCommMonoid α] : CancelCommMonoid (Colex α) := inferInstanceAs CancelCommMonoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [InvolutiveInv
  signature: α] : InvolutiveInv (Colex α)
  body: inferInstanceAs InvolutiveInv α

@[to_additive]

中文:
实例 [InvolutiveInv
  签名: α] : InvolutiveInv (Colex α)
  定义体: inferInstanceAs InvolutiveInv α

@[to_additive]

Depends on / 依赖: InvolutiveInv
-/
instance [InvolutiveInv α] : InvolutiveInv (Colex α) := inferInstanceAs InvolutiveInv α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DivInvMonoid
  signature: α] : DivInvMonoid (Colex α)
  body: inferInstanceAs DivInvMonoid α

@[to_additive]

中文:
实例 [DivInvMonoid
  签名: α] : DivInvMonoid (Colex α)
  定义体: inferInstanceAs DivInvMonoid α

@[to_additive]

Depends on / 依赖: DivInvMonoid
-/
instance [DivInvMonoid α] : DivInvMonoid (Colex α) := inferInstanceAs DivInvMonoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DivisionMonoid
  signature: α] : DivisionMonoid (Colex α)
  body: inferInstanceAs DivisionMonoid α

@[to_additive]

中文:
实例 [DivisionMonoid
  签名: α] : DivisionMonoid (Colex α)
  定义体: inferInstanceAs DivisionMonoid α

@[to_additive]

Depends on / 依赖: DivisionMonoid
-/
instance [DivisionMonoid α] : DivisionMonoid (Colex α) := inferInstanceAs DivisionMonoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DivisionCommMonoid
  signature: α] : DivisionCommMonoid (Colex α)
  body: inferInstanceAs DivisionCommMonoid α

@[to_additive]

中文:
实例 [DivisionCommMonoid
  签名: α] : DivisionCommMonoid (Colex α)
  定义体: inferInstanceAs DivisionCommMonoid α

@[to_additive]

Depends on / 依赖: DivisionCommMonoid
-/
instance [DivisionCommMonoid α] : DivisionCommMonoid (Colex α) :=
inferInstanceAs DivisionCommMonoid α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Group
  signature: α] : Group (Colex α)
  body: inferInstanceAs Group α

@[to_additive]

中文:
实例 [Group
  签名: α] : Group (Colex α)
  定义体: inferInstanceAs Group α

@[to_additive]
-/
instance [Group α] : Group (Colex α) := inferInstanceAs Group α

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommGroup
  signature: α] : CommGroup (Colex α)
  body: inferInstanceAs CommGroup α

中文:
实例 [CommGroup
  签名: α] : CommGroup (Colex α)
  定义体: inferInstanceAs CommGroup α

Depends on / 依赖: CommGroup
-/
instance [CommGroup α] : CommGroup (Colex α) := inferInstanceAs CommGroup α

end Colex

@[to_additive (attr := simp)]
/--
theorem `toColex_one` / 定理 `toColex_one`

English:
theorem toColex_one
  given: [One α]
  statement: toColex (1 : α) = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toColex_one
  条件: [One α]
  结论: toColex (1 : α) = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem toColex_one [One α] : toColex (1 : α) = 1 := rfl

@[to_additive (attr := simp)]
/--
theorem `toColex_eq_one` / 定理 `toColex_eq_one`

English:
theorem toColex_eq_one
  given: [One α] {a : α}
  statement: toColex a = 1 ↔ a = 1
  proof: .rfl

@[to_additive (attr := simp)]

中文:
定理 toColex_eq_one
  条件: [One α] {a : α}
  结论: toColex a = 1 ↔ a = 1
  证明: .rfl

@[to_additive (attr := simp)]
-/
theorem toColex_eq_one [One α] {a : α} : toColex a = 1 ↔ a = 1 := .rfl

@[to_additive (attr := simp)]
/--
theorem `ofColex_one` / 定理 `ofColex_one`

English:
theorem ofColex_one
  given: [One α]
  statement: (ofColex 1 : α) = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 ofColex_one
  条件: [One α]
  结论: (ofColex 1 : α) = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem ofColex_one [One α] : (ofColex 1 : α) = 1 := rfl

@[to_additive (attr := simp)]
/--
theorem `ofColex_eq_one` / 定理 `ofColex_eq_one`

English:
theorem ofColex_eq_one
  given: [One α] {a : Colex α}
  statement: ofColex a = 1 ↔ a = 1
  proof: .rfl

@[to_additive (attr := simp)]

中文:
定理 ofColex_eq_one
  条件: [One α] {a : Colex α}
  结论: ofColex a = 1 ↔ a = 1
  证明: .rfl

@[to_additive (attr := simp)]
-/
theorem ofColex_eq_one [One α] {a : Colex α} : ofColex a = 1 ↔ a = 1 := .rfl

@[to_additive (attr := simp)]
/--
theorem `toColex_mul` / 定理 `toColex_mul`

English:
theorem toColex_mul
  given: [Mul α] (a b : α)
  statement: toColex (a * b) = toColex a * toColex b
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toColex_mul
  条件: [Mul α] (a b : α)
  结论: toColex (a * b) = toColex a * toColex b
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem toColex_mul [Mul α] (a b : α) : toColex (a * b) = toColex a * toColex b := rfl

@[to_additive (attr := simp)]
/--
theorem `ofColex_mul` / 定理 `ofColex_mul`

English:
theorem ofColex_mul
  given: [Mul α] (a b : Colex α)
  statement: ofColex (a * b) = ofColex a * ofColex b
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 ofColex_mul
  条件: [Mul α] (a b : Colex α)
  结论: ofColex (a * b) = ofColex a * ofColex b
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem ofColex_mul [Mul α] (a b : Colex α) : ofColex (a * b) = ofColex a * ofColex b := rfl

@[to_additive (attr := simp)]
/--
theorem `toColex_inv` / 定理 `toColex_inv`

English:
theorem toColex_inv
  given: [Inv α] (a : α)
  statement: toColex a⁻¹ = (toColex a)⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toColex_inv
  条件: [Inv α] (a : α)
  结论: toColex a⁻¹ = (toColex a)⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem toColex_inv [Inv α] (a : α) : toColex a⁻¹ = (toColex a)⁻¹ := rfl

@[to_additive (attr := simp)]
/--
theorem `ofColex_inv` / 定理 `ofColex_inv`

English:
theorem ofColex_inv
  given: [Inv α] (a : Colex α)
  statement: ofColex a⁻¹ = (ofColex a)⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 ofColex_inv
  条件: [Inv α] (a : Colex α)
  结论: ofColex a⁻¹ = (ofColex a)⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem ofColex_inv [Inv α] (a : Colex α) : ofColex a⁻¹ = (ofColex a)⁻¹ := rfl

@[to_additive (attr := simp)]
/--
theorem `toColex_div` / 定理 `toColex_div`

English:
theorem toColex_div
  given: [Div α] (a b : α)
  statement: toColex (a / b) = toColex a / toColex b
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toColex_div
  条件: [Div α] (a b : α)
  结论: toColex (a / b) = toColex a / toColex b
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem toColex_div [Div α] (a b : α) : toColex (a / b) = toColex a / toColex b := rfl

@[to_additive (attr := simp)]
/--
theorem `ofColex_div` / 定理 `ofColex_div`

English:
theorem ofColex_div
  given: [Div α] (a b : Colex α)
  statement: ofColex (a / b) = ofColex a / ofColex b
  proof: rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toColex_smul]

中文:
定理 ofColex_div
  条件: [Div α] (a b : Colex α)
  结论: ofColex (a / b) = ofColex a / ofColex b
  证明: rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toColex_smul]
-/
theorem ofColex_div [Div α] (a b : Colex α) : ofColex (a / b) = ofColex a / ofColex b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toColex_smul]
/--
theorem `toColex_pow` / 定理 `toColex_pow`

English:
theorem toColex_pow
  given: [Pow α β] (a : α) (b : β)
  statement: toColex (a ^ b) = toColex a ^ b
  proof: rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofColex_smul]

中文:
定理 toColex_pow
  条件: [Pow α β] (a : α) (b : β)
  结论: toColex (a ^ b) = toColex a ^ b
  证明: rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofColex_smul]
-/
theorem toColex_pow [Pow α β] (a : α) (b : β) : toColex (a ^ b) = toColex a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofColex_smul]
/--
theorem `ofColex_pow` / 定理 `ofColex_pow`

English:
theorem ofColex_pow
  given: [Pow α β] (a : Colex α) (b : β)
  statement: ofColex (a ^ b) = ofColex a ^ b
  proof: rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toColex_smul']

中文:
定理 ofColex_pow
  条件: [Pow α β] (a : Colex α) (b : β)
  结论: ofColex (a ^ b) = ofColex a ^ b
  证明: rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toColex_smul']
-/
theorem ofColex_pow [Pow α β] (a : Colex α) (b : β) : ofColex (a ^ b) = ofColex a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toColex_smul']
/--
theorem `pow_toColex` / 定理 `pow_toColex`

English:
theorem pow_toColex
  given: [Pow α β] (a : α) (b : β)
  statement: a ^ toColex b = a ^ b
  proof: rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofColex_smul']

中文:
定理 pow_toColex
  条件: [Pow α β] (a : α) (b : β)
  结论: a ^ toColex b = a ^ b
  证明: rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofColex_smul']
-/
theorem pow_toColex [Pow α β] (a : α) (b : β) : a ^ toColex b = a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofColex_smul']
/--
theorem `pow_ofColex` / 定理 `pow_ofColex`

English:
theorem pow_ofColex
  given: [Pow α β] (a : α) (b : Colex β)
  statement: a ^ ofColex b = a ^ b
  proof: rfl

中文:
定理 pow_ofColex
  条件: [Pow α β] (a : α) (b : Colex β)
  结论: a ^ ofColex b = a ^ b
  证明: rfl
-/
theorem pow_ofColex [Pow α β] (a : α) (b : Colex β) : a ^ ofColex b = a ^ b := rfl

section Monoid
variable [Monoid α]

@[to_additive (attr := simp)]
/--
lemma `isLeftRegular_toColex` / 引理 `isLeftRegular_toColex`

English:
lemma isLeftRegular_toColex
  given: {a : α}
  statement: IsLeftRegular (toColex a) ↔ IsLeftRegular a
  proof: .rfl

@[to_additive (attr := simp)]

中文:
引理 isLeftRegular_toColex
  条件: {a : α}
  结论: IsLeftRegular (toColex a) ↔ IsLeftRegular a
  证明: .rfl

@[to_additive (attr := simp)]
-/
lemma isLeftRegular_toColex {a : α} : IsLeftRegular (toColex a) ↔ IsLeftRegular a := .rfl

@[to_additive (attr := simp)]
/--
lemma `isLeftRegular_ofColex` / 引理 `isLeftRegular_ofColex`

English:
lemma isLeftRegular_ofColex
  given: {a : Colex α}
  statement: IsLeftRegular (ofColex a) ↔ IsLeftRegular a
  proof: .rfl

@[to_additive (attr := simp)]

中文:
引理 isLeftRegular_ofColex
  条件: {a : Colex α}
  结论: IsLeftRegular (ofColex a) ↔ IsLeftRegular a
  证明: .rfl

@[to_additive (attr := simp)]
-/
lemma isLeftRegular_ofColex {a : Colex α} : IsLeftRegular (ofColex a) ↔ IsLeftRegular a := .rfl

@[to_additive (attr := simp)]
/--
lemma `isRightRegular_toColex` / 引理 `isRightRegular_toColex`

English:
lemma isRightRegular_toColex
  given: {a : α}
  statement: IsRightRegular (toColex a) ↔ IsRightRegular a
  proof: .rfl

@[to_additive (attr := simp)]

中文:
引理 isRightRegular_toColex
  条件: {a : α}
  结论: IsRightRegular (toColex a) ↔ IsRightRegular a
  证明: .rfl

@[to_additive (attr := simp)]
-/
lemma isRightRegular_toColex {a : α} : IsRightRegular (toColex a) ↔ IsRightRegular a := .rfl

@[to_additive (attr := simp)]
/--
lemma `isRightRegular_ofColex` / 引理 `isRightRegular_ofColex`

English:
lemma isRightRegular_ofColex
  given: {a : Colex α}
  statement: IsRightRegular (ofColex a) ↔ IsRightRegular a
  proof: .rfl

@[to_additive (attr := simp)]

中文:
引理 isRightRegular_ofColex
  条件: {a : Colex α}
  结论: IsRightRegular (ofColex a) ↔ IsRightRegular a
  证明: .rfl

@[to_additive (attr := simp)]
-/
lemma isRightRegular_ofColex {a : Colex α} : IsRightRegular (ofColex a) ↔ IsRightRegular a := .rfl

@[to_additive (attr := simp)]
/--
lemma `isRegular_toColex` / 引理 `isRegular_toColex`

English:
lemma isRegular_toColex
  given: {a : α}
  statement: IsRegular (toColex a) ↔ IsRegular a
  proof: .rfl

@[to_additive (attr := simp)]

中文:
引理 isRegular_toColex
  条件: {a : α}
  结论: IsRegular (toColex a) ↔ IsRegular a
  证明: .rfl

@[to_additive (attr := simp)]
-/
lemma isRegular_toColex {a : α} : IsRegular (toColex a) ↔ IsRegular a := .rfl

@[to_additive (attr := simp)]
/--
lemma `isRegular_ofColex` / 引理 `isRegular_ofColex`

English:
lemma isRegular_ofColex
  given: {a : Colex α}
  statement: IsRegular (ofColex a) ↔ IsRegular a
  proof: .rfl

中文:
引理 isRegular_ofColex
  条件: {a : Colex α}
  结论: IsRegular (ofColex a) ↔ IsRegular a
  证明: .rfl
-/
lemma isRegular_ofColex {a : Colex α} : IsRegular (ofColex a) ↔ IsRegular a := .rfl

end Monoid
