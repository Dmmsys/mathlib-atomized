/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Algebra.Opposites
public import Mathlib.Tactic.Conv

/-!
# Group structures on the multiplicative and additive opposites
-/

public section

assert_not_exists MonoidWithZero DenselyOrdered Units

variable {α : Type*}

namespace MulOpposite


/--
Instance `instAddSemigroup` / 实例 `instAddSemigroup`

English:
instance instAddSemigroup
  signature: [AddSemigroup α]
  body: unop_injective.addSemigroup _ fun _ _ => rfl

中文:
实例 instAddSemigroup
  签名: [AddSemigroup α]
  定义体: unop_injective.addSemigroup _ fun _ _ => rfl

Depends on / 依赖: addSemigroup, unop_injective, unop_injective.addSemigroup
-/
instance instAddSemigroup [AddSemigroup α] : AddSemigroup αᵐᵒᵖ :=
  unop_injective.addSemigroup _ fun _ _ => rfl

/--
Instance `instAddLeftCancelSemigroup` / 实例 `instAddLeftCancelSemigroup`

English:
instance instAddLeftCancelSemigroup
  signature: [AddLeftCancelSemigroup α]
  body: unop_injective.addLeftCancelSemigroup _ fun _ _ => rfl

中文:
实例 instAddLeftCancelSemigroup
  签名: [AddLeftCancelSemigroup α]
  定义体: unop_injective.addLeftCancelSemigroup _ fun _ _ => rfl

Depends on / 依赖: addLeftCancelSemigroup, unop_injective, unop_injective.addLeftCancelSemigroup
-/
instance instAddLeftCancelSemigroup [AddLeftCancelSemigroup α] : AddLeftCancelSemigroup αᵐᵒᵖ :=
  unop_injective.addLeftCancelSemigroup _ fun _ _ => rfl

/--
Instance `instAddRightCancelSemigroup` / 实例 `instAddRightCancelSemigroup`

English:
instance instAddRightCancelSemigroup
  signature: [AddRightCancelSemigroup α]
  body: unop_injective.addRightCancelSemigroup _ fun _ _ => rfl

中文:
实例 instAddRightCancelSemigroup
  签名: [AddRightCancelSemigroup α]
  定义体: unop_injective.addRightCancelSemigroup _ fun _ _ => rfl

Depends on / 依赖: addRightCancelSemigroup, unop_injective, unop_injective.addRightCancelSemigroup
-/
instance instAddRightCancelSemigroup [AddRightCancelSemigroup α] : AddRightCancelSemigroup αᵐᵒᵖ :=
  unop_injective.addRightCancelSemigroup _ fun _ _ => rfl

/--
Instance `instAddCommMagma` / 实例 `instAddCommMagma`

English:
instance instAddCommMagma
  signature: [AddCommMagma α]
  body: unop_injective.addCommMagma _ fun _ _ => rfl

中文:
实例 instAddCommMagma
  签名: [AddCommMagma α]
  定义体: unop_injective.addCommMagma _ fun _ _ => rfl

Depends on / 依赖: addCommMagma, unop_injective, unop_injective.addCommMagma
-/
instance instAddCommMagma [AddCommMagma α] : AddCommMagma αᵐᵒᵖ :=
  unop_injective.addCommMagma _ fun _ _ => rfl

/--
Instance `instAddCommSemigroup` / 实例 `instAddCommSemigroup`

English:
instance instAddCommSemigroup
  signature: [AddCommSemigroup α]
  body: unop_injective.addCommSemigroup _ fun _ _ => rfl

中文:
实例 instAddCommSemigroup
  签名: [AddCommSemigroup α]
  定义体: unop_injective.addCommSemigroup _ fun _ _ => rfl

Depends on / 依赖: addCommSemigroup, unop_injective, unop_injective.addCommSemigroup
-/
instance instAddCommSemigroup [AddCommSemigroup α] : AddCommSemigroup αᵐᵒᵖ :=
  unop_injective.addCommSemigroup _ fun _ _ => rfl

/--
Instance `instAddZeroClass` / 实例 `instAddZeroClass`

English:
instance instAddZeroClass
  signature: [AddZeroClass α]
  body: unop_injective.addZeroClass _ (by exact rfl) fun _ _ => rfl

中文:
实例 instAddZeroClass
  签名: [AddZeroClass α]
  定义体: unop_injective.addZeroClass _ (by exact rfl) fun _ _ => rfl

Depends on / 依赖: addZeroClass, unop_injective, unop_injective.addZeroClass
-/
instance instAddZeroClass [AddZeroClass α] : AddZeroClass αᵐᵒᵖ :=
  unop_injective.addZeroClass _ (by exact rfl) fun _ _ => rfl

/--
Instance `instAddMonoid` / 实例 `instAddMonoid`

English:
instance instAddMonoid
  signature: [AddMonoid α]
  body: unop_injective.addMonoid _ (by exact rfl) (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 instAddMonoid
  签名: [AddMonoid α]
  定义体: unop_injective.addMonoid _ (by exact rfl) (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: addMonoid, unop_injective, unop_injective.addMonoid
-/
instance instAddMonoid [AddMonoid α] : AddMonoid αᵐᵒᵖ :=
  unop_injective.addMonoid _ (by exact rfl) (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `instAddCommMonoid` / 实例 `instAddCommMonoid`

English:
instance instAddCommMonoid
  signature: [AddCommMonoid α]
  body: unop_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 instAddCommMonoid
  签名: [AddCommMonoid α]
  定义体: unop_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: addCommMonoid, unop_injective, unop_injective.addCommMonoid
-/
instance instAddCommMonoid [AddCommMonoid α] : AddCommMonoid αᵐᵒᵖ :=
  unop_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `instSubNegMonoid` / 实例 `instSubNegMonoid`

English:
instance instSubNegMonoid
  signature: [SubNegMonoid α]
  body: unop_injective.subNegMonoid _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 instSubNegMonoid
  签名: [SubNegMonoid α]
  定义体: unop_injective.subNegMonoid _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: subNegMonoid, unop_injective, unop_injective.subNegMonoid
-/
instance instSubNegMonoid [SubNegMonoid α] : SubNegMonoid αᵐᵒᵖ :=
  unop_injective.subNegMonoid _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `instAddGroup` / 实例 `instAddGroup`

English:
instance instAddGroup
  signature: [AddGroup α]
  body: unop_injective.addGroup _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
  (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 instAddGroup
  签名: [AddGroup α]
  定义体: unop_injective.addGroup _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
  (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: addGroup, unop_injective, unop_injective.addGroup
-/
instance instAddGroup [AddGroup α] : AddGroup αᵐᵒᵖ :=
  unop_injective.addGroup _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
  (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: [AddCommGroup α]
  body: unop_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 instAddCommGroup
  签名: [AddCommGroup α]
  定义体: unop_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: addCommGroup, unop_injective, unop_injective.addCommGroup
-/
instance instAddCommGroup [AddCommGroup α] : AddCommGroup αᵐᵒᵖ :=
  unop_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

/-!
### Multiplicative structures on `αᵐᵒᵖ`

We also generate additive structures on `αᵃᵒᵖ` using `to_additive`
-/

@[to_additive]
/--
Instance `instIsRightCancelMul` / 实例 `instIsRightCancelMul`

English:
instance instIsRightCancelMul
  signature: [Mul α] [IsLeftCancelMul α]
  body: unop_injective mul_left_cancel op_injective h

@[to_additive]

中文:
实例 instIsRightCancelMul
  签名: [Mul α] [IsLeftCancelMul α]
  定义体: unop_injective mul_left_cancel op_injective h

@[to_additive]

Depends on / 依赖: mul_left_cancel, op_injective, unop_injective
-/
instance instIsRightCancelMul [Mul α] [IsLeftCancelMul α] : IsRightCancelMul αᵐᵒᵖ where
mul_right_cancel _ _ _ h := unop_injective mul_left_cancel op_injective h

@[to_additive]
/--
Instance `instIsLeftCancelMul` / 实例 `instIsLeftCancelMul`

English:
instance instIsLeftCancelMul
  signature: [Mul α] [IsRightCancelMul α]
  body: unop_injective mul_right_cancel op_injective h

中文:
实例 instIsLeftCancelMul
  签名: [Mul α] [IsRightCancelMul α]
  定义体: unop_injective mul_right_cancel op_injective h

Depends on / 依赖: mul_right_cancel, op_injective, unop_injective
-/
instance instIsLeftCancelMul [Mul α] [IsRightCancelMul α] : IsLeftCancelMul αᵐᵒᵖ where
mul_left_cancel _ _ _ h := unop_injective mul_right_cancel op_injective h

/--
Instance `instIsCancelMul` / 实例 `instIsCancelMul`

English:
instance instIsCancelMul
  signature: [Mul α] [IsCancelMul α]

中文:
实例 instIsCancelMul
  签名: [Mul α] [IsCancelMul α]
-/
@[to_additive] instance instIsCancelMul [Mul α] [IsCancelMul α] : IsCancelMul αᵐᵒᵖ where

@[to_additive]
/--
Instance `instSemigroup` / 实例 `instSemigroup`

English:
instance instSemigroup
  signature: [Semigroup α]
  body: unop_injective Eq.symm mul_assoc (unop z) (unop y) (unop x)

@[to_additive]

中文:
实例 instSemigroup
  签名: [Semigroup α]
  定义体: unop_injective Eq.symm mul_assoc (unop z) (unop y) (unop x)

@[to_additive]

Depends on / 依赖: Eq.symm, mul_assoc, unop_injective
-/
instance instSemigroup [Semigroup α] : Semigroup αᵐᵒᵖ where
mul_assoc x y z := unop_injective Eq.symm mul_assoc (unop z) (unop y) (unop x)

@[to_additive]
/--
Instance `instLeftCancelSemigroup` / 实例 `instLeftCancelSemigroup`

English:
instance instLeftCancelSemigroup
  signature: [RightCancelSemigroup α]
  body: mul_left_cancel

@[to_additive]

中文:
实例 instLeftCancelSemigroup
  签名: [RightCancelSemigroup α]
  定义体: mul_left_cancel

@[to_additive]

Depends on / 依赖: mul_left_cancel
-/
instance instLeftCancelSemigroup [RightCancelSemigroup α] : LeftCancelSemigroup αᵐᵒᵖ where
  mul_left_cancel _ _ _ := mul_left_cancel

@[to_additive]
/--
Instance `instRightCancelSemigroup` / 实例 `instRightCancelSemigroup`

English:
instance instRightCancelSemigroup
  signature: [LeftCancelSemigroup α]
  body: mul_right_cancel

@[to_additive]

中文:
实例 instRightCancelSemigroup
  签名: [LeftCancelSemigroup α]
  定义体: mul_right_cancel

@[to_additive]

Depends on / 依赖: mul_right_cancel
-/
instance instRightCancelSemigroup [LeftCancelSemigroup α] : RightCancelSemigroup αᵐᵒᵖ where
  mul_right_cancel _ _ _ := mul_right_cancel

@[to_additive]
/--
Instance `instCommSemigroup` / 实例 `instCommSemigroup`

English:
instance instCommSemigroup
  signature: [CommSemigroup α]
  body: unop_injective mul_comm (unop y) (unop x)

中文:
实例 instCommSemigroup
  签名: [CommSemigroup α]
  定义体: unop_injective mul_comm (unop y) (unop x)

Depends on / 依赖: mul_comm, unop_injective
-/
instance instCommSemigroup [CommSemigroup α] : CommSemigroup αᵐᵒᵖ where
mul_comm x y := unop_injective mul_comm (unop y) (unop x)

/--
Instance `instMulOne` / 实例 `instMulOne`

English:
instance instMulOne
  signature: [MulOne α]

中文:
实例 instMulOne
  签名: [MulOne α]
-/
@[to_additive] instance instMulOne [MulOne α] : MulOne αᵐᵒᵖ where

@[to_additive]
/--
Instance `instMulOneClass` / 实例 `instMulOneClass`

English:
instance instMulOneClass
  signature: [MulOneClass α]
  body: unop_injective mul_one _
mul_one _ := unop_injective one_mul _

@[to_additive]

中文:
实例 instMulOneClass
  签名: [MulOneClass α]
  定义体: unop_injective mul_one _
mul_one _ := unop_injective one_mul _

@[to_additive]

Depends on / 依赖: mul_one, unop_injective
-/
instance instMulOneClass [MulOneClass α] : MulOneClass αᵐᵒᵖ where
one_mul _ := unop_injective mul_one _
mul_one _ := unop_injective one_mul _

@[to_additive]
/--
Instance `instMonoid` / 实例 `instMonoid`

English:
instance instMonoid
  signature: [Monoid α]
  body: instSemigroup
  __ := instMulOneClass
npow n a := op a.unop ^ n
npow_zero _ := unop_injective pow_zero _
npow_succ _ _ := unop_injective pow_succ' _ _

@[to_additive]

中文:
实例 instMonoid
  签名: [Monoid α]
  定义体: instSemigroup
  __ := instMulOneClass
npow n a := op a.unop ^ n
npow_zero _ := unop_injective pow_zero _
npow_succ _ _ := unop_injective pow_succ' _ _

@[to_additive]

Depends on / 依赖: instSemigroup
-/
instance instMonoid [Monoid α] : Monoid αᵐᵒᵖ where
  toSemigroup := instSemigroup
  __ := instMulOneClass
npow n a := op a.unop ^ n
npow_zero _ := unop_injective pow_zero _
npow_succ _ _ := unop_injective pow_succ' _ _

@[to_additive]
/--
Instance `instLeftCancelMonoid` / 实例 `instLeftCancelMonoid`

English:
instance instLeftCancelMonoid
  signature: [RightCancelMonoid α]
  body: instMonoid
  __ := instLeftCancelSemigroup

@[to_additive]

中文:
实例 instLeftCancelMonoid
  签名: [RightCancelMonoid α]
  定义体: instMonoid
  __ := instLeftCancelSemigroup

@[to_additive]

Depends on / 依赖: instMonoid
-/
instance instLeftCancelMonoid [RightCancelMonoid α] : LeftCancelMonoid αᵐᵒᵖ where
  toMonoid := instMonoid
  __ := instLeftCancelSemigroup

@[to_additive]
/--
Instance `instRightCancelMonoid` / 实例 `instRightCancelMonoid`

English:
instance instRightCancelMonoid
  signature: [LeftCancelMonoid α]
  body: instMonoid
  __ := instRightCancelSemigroup

@[to_additive]

中文:
实例 instRightCancelMonoid
  签名: [LeftCancelMonoid α]
  定义体: instMonoid
  __ := instRightCancelSemigroup

@[to_additive]

Depends on / 依赖: instMonoid
-/
instance instRightCancelMonoid [LeftCancelMonoid α] : RightCancelMonoid αᵐᵒᵖ where
  toMonoid := instMonoid
  __ := instRightCancelSemigroup

@[to_additive]
/--
Instance `instCancelMonoid` / 实例 `instCancelMonoid`

English:
instance instCancelMonoid
  signature: [CancelMonoid α]
  body: instLeftCancelMonoid
  __ := instRightCancelMonoid

@[to_additive]

中文:
实例 instCancelMonoid
  签名: [CancelMonoid α]
  定义体: instLeftCancelMonoid
  __ := instRightCancelMonoid

@[to_additive]

Depends on / 依赖: instLeftCancelMonoid
-/
instance instCancelMonoid [CancelMonoid α] : CancelMonoid αᵐᵒᵖ where
  toLeftCancelMonoid := instLeftCancelMonoid
  __ := instRightCancelMonoid

@[to_additive]
/--
Instance `instCommMonoid` / 实例 `instCommMonoid`

English:
instance instCommMonoid
  signature: [CommMonoid α]
  body: instMonoid
  __ := instCommSemigroup

@[to_additive]

中文:
实例 instCommMonoid
  签名: [CommMonoid α]
  定义体: instMonoid
  __ := instCommSemigroup

@[to_additive]

Depends on / 依赖: instMonoid
-/
instance instCommMonoid [CommMonoid α] : CommMonoid αᵐᵒᵖ where
  toMonoid := instMonoid
  __ := instCommSemigroup

@[to_additive]
/--
Instance `instCancelCommMonoid` / 实例 `instCancelCommMonoid`

English:
instance instCancelCommMonoid
  signature: [CancelCommMonoid α]
  body: instCommMonoid
  __ := instLeftCancelMonoid

@[to_additive AddOpposite.instSubNegMonoid]

中文:
实例 instCancelCommMonoid
  签名: [CancelCommMonoid α]
  定义体: instCommMonoid
  __ := instLeftCancelMonoid

@[to_additive AddOpposite.instSubNegMonoid]

Depends on / 依赖: instCommMonoid
-/
instance instCancelCommMonoid [CancelCommMonoid α] : CancelCommMonoid αᵐᵒᵖ where
  toCommMonoid := instCommMonoid
  __ := instLeftCancelMonoid

@[to_additive AddOpposite.instSubNegMonoid]
/--
Instance `instDivInvMonoid` / 实例 `instDivInvMonoid`

English:
instance instDivInvMonoid
  signature: [DivInvMonoid α]
  body: instMonoid
  toInv := instInv
zpow n a := op a.unop ^ n
zpow_zero' _ := unop_injective zpow_zero _
zpow_succ' _ _ := unop_injective by
    simp_rw [HPow.hPow, Pow.pow]
    rw [unop_op]; rw [zpow_natCast]; rw [pow_succ']; rw [unop_mul]; rw [unop_op]; rw [zpow_natCast]
zpow_neg' _ _ := unop_injective 

中文:
实例 instDivInvMonoid
  签名: [DivInvMonoid α]
  定义体: instMonoid
  toInv := instInv
zpow n a := op a.unop ^ n
zpow_zero' _ := unop_injective zpow_zero _
zpow_succ' _ _ := unop_injective by
    simp_rw [HPow.hPow, Pow.pow]
    rw [unop_op]; rw [zpow_natCast]; rw [pow_succ']; rw [unop_mul]; rw [unop_op]; rw [zpow_natCast]
zpow_neg' _ _ := unop_injective 

Depends on / 依赖: instMonoid
-/
instance instDivInvMonoid [DivInvMonoid α] : DivInvMonoid αᵐᵒᵖ where
  toMonoid := instMonoid
  toInv := instInv
zpow n a := op a.unop ^ n
zpow_zero' _ := unop_injective zpow_zero _
zpow_succ' _ _ := unop_injective by
    simp_rw [HPow.hPow, Pow.pow]
    rw [unop_op]; rw [zpow_natCast]; rw [pow_succ']; rw [unop_mul]; rw [unop_op]; rw [zpow_natCast]
zpow_neg' _ _ := unop_injective DivInvMonoid.zpow_neg' _ _

@[to_additive]
/--
Instance `instDivisionMonoid` / 实例 `instDivisionMonoid`

English:
instance instDivisionMonoid
  signature: [DivisionMonoid α]
  body: instDivInvMonoid
  __ := instInvolutiveInv
mul_inv_rev _ _ := unop_injective mul_inv_rev _ _
inv_eq_of_mul _ _ h := unop_injective inv_eq_of_mul_eq_one_left congr_arg unop h

@[to_additive AddOpposite.instSubtractionCommMonoid]

中文:
实例 instDivisionMonoid
  签名: [DivisionMonoid α]
  定义体: instDivInvMonoid
  __ := instInvolutiveInv
mul_inv_rev _ _ := unop_injective mul_inv_rev _ _
inv_eq_of_mul _ _ h := unop_injective inv_eq_of_mul_eq_one_left congr_arg unop h

@[to_additive AddOpposite.instSubtractionCommMonoid]

Depends on / 依赖: instDivInvMonoid
-/
instance instDivisionMonoid [DivisionMonoid α] : DivisionMonoid αᵐᵒᵖ where
  toDivInvMonoid := instDivInvMonoid
  __ := instInvolutiveInv
mul_inv_rev _ _ := unop_injective mul_inv_rev _ _
inv_eq_of_mul _ _ h := unop_injective inv_eq_of_mul_eq_one_left congr_arg unop h

@[to_additive AddOpposite.instSubtractionCommMonoid]
/--
Instance `instDivisionCommMonoid` / 实例 `instDivisionCommMonoid`

English:
instance instDivisionCommMonoid
  signature: [DivisionCommMonoid α]
  body: instDivisionMonoid
  __ := instCommSemigroup

@[to_additive]

中文:
实例 instDivisionCommMonoid
  签名: [DivisionCommMonoid α]
  定义体: instDivisionMonoid
  __ := instCommSemigroup

@[to_additive]

Depends on / 依赖: instDivisionMonoid
-/
instance instDivisionCommMonoid [DivisionCommMonoid α] : DivisionCommMonoid αᵐᵒᵖ where
  toDivisionMonoid := instDivisionMonoid
  __ := instCommSemigroup

@[to_additive]
/--
Instance `instGroup` / 实例 `instGroup`

English:
instance instGroup
  signature: [Group α]
  body: instDivInvMonoid
inv_mul_cancel _ := unop_injective mul_inv_cancel _

@[to_additive]

中文:
实例 instGroup
  签名: [Group α]
  定义体: instDivInvMonoid
inv_mul_cancel _ := unop_injective mul_inv_cancel _

@[to_additive]

Depends on / 依赖: instDivInvMonoid
-/
instance instGroup [Group α] : Group αᵐᵒᵖ where
  toDivInvMonoid := instDivInvMonoid
inv_mul_cancel _ := unop_injective mul_inv_cancel _

@[to_additive]
/--
Instance `instCommGroup` / 实例 `instCommGroup`

English:
instance instCommGroup
  signature: [CommGroup α]
  body: instGroup
  __ := instCommSemigroup

中文:
实例 instCommGroup
  签名: [CommGroup α]
  定义体: instGroup
  __ := instCommSemigroup

Depends on / 依赖: instGroup
-/
instance instCommGroup [CommGroup α] : CommGroup αᵐᵒᵖ where
  toGroup := instGroup
  __ := instCommSemigroup

section Monoid
variable [Monoid α]

/--
lemma `op_pow` / 引理 `op_pow`

English:
lemma op_pow
  given: (x : α) (n : Nat)
  statement: op (x ^ n) = op x ^ n
  proof: rfl

中文:
引理 op_pow
  条件: (x : α) (n : 自然数)
  结论: op (x ^ n) = op x ^ n
  证明: rfl
-/
@[to_additive (attr := simp)] lemma op_pow (x : α) (n : Nat) : op (x ^ n) = op x ^ n := rfl

/--
lemma `unop_pow` / 引理 `unop_pow`

English:
lemma unop_pow
  given: (x : αᵐᵒᵖ) (n : Nat)
  statement: unop (x ^ n) = unop x ^ n
  proof: rfl

中文:
引理 unop_pow
  条件: (x : αᵐᵒᵖ) (n : 自然数)
  结论: unop (x ^ n) = unop x ^ n
  证明: rfl

Depends on / 依赖: Nonempty, Nonempty.image2, image2
-/
@[to_additive (attr := simp)] lemma unop_pow (x : αᵐᵒᵖ) (n : Nat) : unop (x ^ n) = unop x ^ n := rfl

end Monoid

section DivInvMonoid
variable [DivInvMonoid α]

/--
lemma `op_zpow` / 引理 `op_zpow`

English:
lemma op_zpow
  given: (x : α) (z : Int)
  statement: op (x ^ z) = op x ^ z
  proof: rfl

中文:
引理 op_zpow
  条件: (x : α) (z : 整数)
  结论: op (x ^ z) = op x ^ z
  证明: rfl

Depends on / 依赖: Nonempty, Nonempty.of_image2_left, of_image2_left
-/
@[to_additive (attr := simp)] lemma op_zpow (x : α) (z : Int) : op (x ^ z) = op x ^ z := rfl

/--
lemma `unop_zpow` / 引理 `unop_zpow`

English:
lemma unop_zpow
  given: (x : αᵐᵒᵖ) (z : Int)
  statement: unop (x ^ z) = unop x ^ z
  proof: rfl

中文:
引理 unop_zpow
  条件: (x : αᵐᵒᵖ) (z : 整数)
  结论: unop (x ^ z) = unop x ^ z
  证明: rfl

Depends on / 依赖: Nonempty, Nonempty.of_image2_right, of_image2_right
-/
@[to_additive (attr := simp)] lemma unop_zpow (x : αᵐᵒᵖ) (z : Int) : unop (x ^ z) = unop x ^ z := rfl

end DivInvMonoid

@[to_additive (attr := simp)]
/--
theorem `unop_div` / 定理 `unop_div`

English:
theorem unop_div
  given: [DivInvMonoid α] (x y : αᵐᵒᵖ)
  statement: unop (x / y) = (unop y)⁻¹ * unop x
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 unop_div
  条件: [DivInvMonoid α] (x y : αᵐᵒᵖ)
  结论: unop (x / y) = (unop y)⁻¹ * unop x
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem unop_div [DivInvMonoid α] (x y : αᵐᵒᵖ) : unop (x / y) = (unop y)⁻¹ * unop x :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `op_div` / 定理 `op_div`

English:
theorem op_div
  given: [DivInvMonoid α] (x y : α)
  statement: op (x / y) = (op y)⁻¹ * op x
  proof: by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

中文:
定理 op_div
  条件: [DivInvMonoid α] (x y : α)
  结论: op (x / y) = (op y)⁻¹ * op x
  证明: by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv
-/
theorem op_div [DivInvMonoid α] (x y : α) : op (x / y) = (op y)⁻¹ * op x := by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/--
theorem `semiconjBy_op` / 定理 `semiconjBy_op`

English:
theorem semiconjBy_op
  given: [Mul α] {a x y : α}
  statement: SemiconjBy (op a) (op y) (op x) ↔ SemiconjBy a x y
  proof: by
  simp only [SemiconjBy, ← op_mul, op_inj, eq_comm]

@[to_additive (attr := simp, nolint simpComm)]

中文:
定理 semiconjBy_op
  条件: [Mul α] {a x y : α}
  结论: SemiconjBy (op a) (op y) (op x) ↔ SemiconjBy a x y
  证明: by
  simp only [SemiconjBy, ← op_mul, op_inj, eq_comm]

@[to_additive (attr := simp, nolint simpComm)]

Depends on / 依赖: SemiconjBy, eq_comm, op_inj, op_mul
-/
theorem semiconjBy_op [Mul α] {a x y : α} : SemiconjBy (op a) (op y) (op x) ↔ SemiconjBy a x y := by
  simp only [SemiconjBy, ← op_mul, op_inj, eq_comm]

@[to_additive (attr := simp, nolint simpComm)]
/--
theorem `semiconjBy_unop` / 定理 `semiconjBy_unop`

English:
theorem semiconjBy_unop
  given: [Mul α] {a x y : αᵐᵒᵖ}
  proof: by
  conv_rhs => rw [← op_unop a, ← op_unop x, ← op_unop y, semiconjBy_op]

中文:
定理 semiconjBy_unop
  条件: [Mul α] {a x y : αᵐᵒᵖ}
  证明: by
  conv_rhs => rw [← op_unop a, ← op_unop x, ← op_unop y, semiconjBy_op]

Depends on / 依赖: conv_rhs, op_unop, semiconjBy_op
-/
theorem semiconjBy_unop [Mul α] {a x y : αᵐᵒᵖ} :
    SemiconjBy (unop a) (unop y) (unop x) ↔ SemiconjBy a x y := by
  conv_rhs => rw [← op_unop a, ← op_unop x, ← op_unop y, semiconjBy_op]

attribute [nolint simpComm] AddOpposite.addSemiconjBy_unop

@[to_additive]
/--
theorem `_root_.SemiconjBy.op` / 定理 `_root_.SemiconjBy.op`

English:
theorem _root_.SemiconjBy.op
  given: [Mul α] {a x y : α} (h : SemiconjBy a x y)
  proof: semiconjBy_op.2 h

@[to_additive]

中文:
定理 _root_.SemiconjBy.op
  条件: [Mul α] {a x y : α} (h : SemiconjBy a x y)
  证明: semiconjBy_op.2 h

@[to_additive]

Depends on / 依赖: semiconjBy_op
-/
theorem _root_.SemiconjBy.op [Mul α] {a x y : α} (h : SemiconjBy a x y) :
    SemiconjBy (op a) (op y) (op x) :=
  semiconjBy_op.2 h

@[to_additive]
/--
theorem `_root_.SemiconjBy.unop` / 定理 `_root_.SemiconjBy.unop`

English:
theorem _root_.SemiconjBy.unop
  given: [Mul α] {a x y : αᵐᵒᵖ} (h : SemiconjBy a x y)
  proof: semiconjBy_unop.2 h

@[to_additive]

中文:
定理 _root_.SemiconjBy.unop
  条件: [Mul α] {a x y : αᵐᵒᵖ} (h : SemiconjBy a x y)
  证明: semiconjBy_unop.2 h

@[to_additive]

Depends on / 依赖: semiconjBy_unop
-/
theorem _root_.SemiconjBy.unop [Mul α] {a x y : αᵐᵒᵖ} (h : SemiconjBy a x y) :
    SemiconjBy (unop a) (unop y) (unop x) :=
  semiconjBy_unop.2 h

@[to_additive]
/--
theorem `_root_.Commute.op` / 定理 `_root_.Commute.op`

English:
theorem _root_.Commute.op
  given: [Mul α] {x y : α} (h : Commute x y)
  statement: Commute (op x) (op y)
  proof: SemiconjBy.op h

@[to_additive]
nonrec theorem _root_.Commute.unop [Mul α] {x y : αᵐᵒᵖ} (h : Commute x y) :
    Commute (unop x) (unop y) :=
  h.unop

@[to_additive (attr := simp)]

中文:
定理 _root_.Commute.op
  条件: [Mul α] {x y : α} (h : Commute x y)
  结论: Commute (op x) (op y)
  证明: SemiconjBy.op h

@[to_additive]
nonrec theorem _root_.Commute.unop [Mul α] {x y : αᵐᵒᵖ} (h : Commute x y) :
    Commute (unop x) (unop y) :=
  h.unop

@[to_additive (attr := simp)]

Depends on / 依赖: SemiconjBy, SemiconjBy.op
-/
theorem _root_.Commute.op [Mul α] {x y : α} (h : Commute x y) : Commute (op x) (op y) :=
  SemiconjBy.op h

@[to_additive]
nonrec theorem _root_.Commute.unop [Mul α] {x y : αᵐᵒᵖ} (h : Commute x y) :
    Commute (unop x) (unop y) :=
  h.unop

@[to_additive (attr := simp)]
/--
theorem `commute_op` / 定理 `commute_op`

English:
theorem commute_op
  given: [Mul α] {x y : α}
  statement: Commute (op x) (op y) ↔ Commute x y
  proof: semiconjBy_op

@[to_additive (attr := simp, nolint simpComm)]

中文:
定理 commute_op
  条件: [Mul α] {x y : α}
  结论: Commute (op x) (op y) ↔ Commute x y
  证明: semiconjBy_op

@[to_additive (attr := simp, nolint simpComm)]

Depends on / 依赖: semiconjBy_op
-/
theorem commute_op [Mul α] {x y : α} : Commute (op x) (op y) ↔ Commute x y :=
  semiconjBy_op

@[to_additive (attr := simp, nolint simpComm)]
/--
theorem `commute_unop` / 定理 `commute_unop`

English:
theorem commute_unop
  given: [Mul α] {x y : αᵐᵒᵖ}
  statement: Commute (unop x) (unop y) ↔ Commute x y
  proof: semiconjBy_unop

中文:
定理 commute_unop
  条件: [Mul α] {x y : αᵐᵒᵖ}
  结论: Commute (unop x) (unop y) ↔ Commute x y
  证明: semiconjBy_unop

Depends on / 依赖: semiconjBy_unop
-/
theorem commute_unop [Mul α] {x y : αᵐᵒᵖ} : Commute (unop x) (unop y) ↔ Commute x y :=
  semiconjBy_unop

attribute [nolint simpComm] AddOpposite.addCommute_unop

/--
theorem `isDedekindFiniteMonoid_iff` / 定理 `isDedekindFiniteMonoid_iff`

English:
theorem isDedekindFiniteMonoid_iff
  given: [MulOne α]
  proof: by
  simp_rw [isDedekindFiniteMonoid_iff, ← opEquiv.forall_congr_right]
  simpa [← op_one, ← op_mul] using forall_comm

中文:
定理 isDedekindFiniteMonoid_iff
  条件: [MulOne α]
  证明: by
  simp_rw [isDedekindFiniteMonoid_iff, ← opEquiv.forall_congr_right]
  simpa [← op_one, ← op_mul] using forall_comm
-/
@[to_additive] protected theorem isDedekindFiniteMonoid_iff [MulOne α] :
    IsDedekindFiniteMonoid αᵐᵒᵖ ↔ IsDedekindFiniteMonoid α := by
  simp_rw [isDedekindFiniteMonoid_iff, ← opEquiv.forall_congr_right]
  simpa [← op_one, ← op_mul] using forall_comm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulOne
  signature: α] [IsDedekindFiniteMonoid α] : IsDedekindFiniteMonoid αᵐᵒᵖ
  body: MulOpposite.isDedekindFiniteMonoid_iff.mpr ‹_›

中文:
实例 [MulOne
  签名: α] [IsDedekindFiniteMonoid α] : IsDedekindFiniteMonoid αᵐᵒᵖ
  定义体: MulOpposite.isDedekindFiniteMonoid_iff.mpr ‹_›
-/
@[to_additive] instance [MulOne α] [IsDedekindFiniteMonoid α] : IsDedekindFiniteMonoid αᵐᵒᵖ :=
  MulOpposite.isDedekindFiniteMonoid_iff.mpr ‹_›

end MulOpposite

/-!
### Multiplicative structures on `αᵃᵒᵖ`
-/


namespace AddOpposite

/--
Instance `instSemigroup` / 实例 `instSemigroup`

English:
instance instSemigroup
  signature: [Semigroup α]
  body: unop_injective.semigroup _ fun _ _ => rfl

中文:
实例 instSemigroup
  签名: [Semigroup α]
  定义体: unop_injective.semigroup _ fun _ _ => rfl

Depends on / 依赖: semigroup, unop_injective, unop_injective.semigroup
-/
instance instSemigroup [Semigroup α] : Semigroup αᵃᵒᵖ := unop_injective.semigroup _ fun _ _ => rfl

/--
Instance `instLeftCancelSemigroup` / 实例 `instLeftCancelSemigroup`

English:
instance instLeftCancelSemigroup
  signature: [LeftCancelSemigroup α]
  body: unop_injective.leftCancelSemigroup _ fun _ _ => rfl

中文:
实例 instLeftCancelSemigroup
  签名: [LeftCancelSemigroup α]
  定义体: unop_injective.leftCancelSemigroup _ fun _ _ => rfl

Depends on / 依赖: leftCancelSemigroup, unop_injective, unop_injective.leftCancelSemigroup
-/
instance instLeftCancelSemigroup [LeftCancelSemigroup α] : LeftCancelSemigroup αᵃᵒᵖ :=
  unop_injective.leftCancelSemigroup _ fun _ _ => rfl

/--
Instance `instRightCancelSemigroup` / 实例 `instRightCancelSemigroup`

English:
instance instRightCancelSemigroup
  signature: [RightCancelSemigroup α]
  body: unop_injective.rightCancelSemigroup _ fun _ _ => rfl

中文:
实例 instRightCancelSemigroup
  签名: [RightCancelSemigroup α]
  定义体: unop_injective.rightCancelSemigroup _ fun _ _ => rfl

Depends on / 依赖: rightCancelSemigroup, unop_injective, unop_injective.rightCancelSemigroup
-/
instance instRightCancelSemigroup [RightCancelSemigroup α] : RightCancelSemigroup αᵃᵒᵖ :=
  unop_injective.rightCancelSemigroup _ fun _ _ => rfl

/--
Instance `instCommSemigroup` / 实例 `instCommSemigroup`

English:
instance instCommSemigroup
  signature: [CommSemigroup α]
  body: unop_injective.commSemigroup _ fun _ _ => rfl

中文:
实例 instCommSemigroup
  签名: [CommSemigroup α]
  定义体: unop_injective.commSemigroup _ fun _ _ => rfl

Depends on / 依赖: commSemigroup, unop_injective, unop_injective.commSemigroup
-/
instance instCommSemigroup [CommSemigroup α] : CommSemigroup αᵃᵒᵖ :=
  unop_injective.commSemigroup _ fun _ _ => rfl

/--
Instance `instMulOneClass` / 实例 `instMulOneClass`

English:
instance instMulOneClass
  signature: [MulOneClass α]
  body: unop_injective.mulOneClass _ (by exact rfl) fun _ _ => rfl

中文:
实例 instMulOneClass
  签名: [MulOneClass α]
  定义体: unop_injective.mulOneClass _ (by exact rfl) fun _ _ => rfl

Depends on / 依赖: mulOneClass, unop_injective, unop_injective.mulOneClass
-/
instance instMulOneClass [MulOneClass α] : MulOneClass αᵃᵒᵖ :=
  unop_injective.mulOneClass _ (by exact rfl) fun _ _ => rfl

/--
Instance `pow` / 实例 `pow`

English:
instance pow
  signature: {β} [Pow α β]
  body: op (unop a ^ b)

@[simp]

中文:
实例 pow
  签名: {β} [Pow α β]
  定义体: op (unop a ^ b)

@[simp]
-/
instance pow {β} [Pow α β] : Pow αᵃᵒᵖ β where pow a b := op (unop a ^ b)

@[simp]
/--
theorem `op_pow` / 定理 `op_pow`

English:
theorem op_pow
  given: {β} [Pow α β] (a : α) (b : β)
  statement: op (a ^ b) = op a ^ b
  proof: rfl

@[simp]

中文:
定理 op_pow
  条件: {β} [Pow α β] (a : α) (b : β)
  结论: op (a ^ b) = op a ^ b
  证明: rfl

@[simp]
-/
theorem op_pow {β} [Pow α β] (a : α) (b : β) : op (a ^ b) = op a ^ b :=
  rfl

@[simp]
/--
theorem `unop_pow` / 定理 `unop_pow`

English:
theorem unop_pow
  given: {β} [Pow α β] (a : αᵃᵒᵖ) (b : β)
  statement: unop (a ^ b) = unop a ^ b
  proof: rfl

中文:
定理 unop_pow
  条件: {β} [Pow α β] (a : αᵃᵒᵖ) (b : β)
  结论: unop (a ^ b) = unop a ^ b
  证明: rfl
-/
theorem unop_pow {β} [Pow α β] (a : αᵃᵒᵖ) (b : β) : unop (a ^ b) = unop a ^ b :=
  rfl

/--
Instance `instMonoid` / 实例 `instMonoid`

English:
instance instMonoid
  signature: [Monoid α]
  body: unop_injective.monoid _ (by exact rfl) (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 instMonoid
  签名: [Monoid α]
  定义体: unop_injective.monoid _ (by exact rfl) (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: monoid, unop_injective, unop_injective.monoid
-/
instance instMonoid [Monoid α] : Monoid αᵃᵒᵖ :=
  unop_injective.monoid _ (by exact rfl) (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `instCommMonoid` / 实例 `instCommMonoid`

English:
instance instCommMonoid
  signature: [CommMonoid α]
  body: unop_injective.commMonoid _ (by exact rfl) (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 instCommMonoid
  签名: [CommMonoid α]
  定义体: unop_injective.commMonoid _ (by exact rfl) (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: commMonoid, unop_injective, unop_injective.commMonoid
-/
instance instCommMonoid [CommMonoid α] : CommMonoid αᵃᵒᵖ :=
  unop_injective.commMonoid _ (by exact rfl) (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `instDivInvMonoid` / 实例 `instDivInvMonoid`

English:
instance instDivInvMonoid
  signature: [DivInvMonoid α]
  body: unop_injective.divInvMonoid _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 instDivInvMonoid
  签名: [DivInvMonoid α]
  定义体: unop_injective.divInvMonoid _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: divInvMonoid, unop_injective, unop_injective.divInvMonoid
-/
instance instDivInvMonoid [DivInvMonoid α] : DivInvMonoid αᵃᵒᵖ :=
  unop_injective.divInvMonoid _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `instGroup` / 实例 `instGroup`

English:
instance instGroup
  signature: [Group α]
  body: unop_injective.group _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 instGroup
  签名: [Group α]
  定义体: unop_injective.group _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: unop_injective, unop_injective.group
-/
instance instGroup [Group α] : Group αᵃᵒᵖ :=
  unop_injective.group _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `instCommGroup` / 实例 `instCommGroup`

English:
instance instCommGroup
  signature: [CommGroup α]
  body: unop_injective.commGroup _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]

中文:
实例 instCommGroup
  签名: [CommGroup α]
  定义体: unop_injective.commGroup _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]

Depends on / 依赖: commGroup, unop_injective, unop_injective.commGroup
-/
instance instCommGroup [CommGroup α] : CommGroup αᵃᵒᵖ :=
  unop_injective.commGroup _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
/--
Instance `instMulTorsionFree` / 实例 `instMulTorsionFree`

English:
instance instMulTorsionFree
  signature: [Monoid α] [IsMulTorsionFree α]
  body: ⟨fun _ h => op_injective.comp (pow_left_injective h).comp unop_injective⟩

中文:
实例 instMulTorsionFree
  签名: [Monoid α] [IsMulTorsionFree α]
  定义体: ⟨fun _ h => op_injective.comp (pow_left_injective h).comp unop_injective⟩

Depends on / 依赖: op_injective, op_injective.comp, pow_left_injective, unop_injective
-/
instance instMulTorsionFree [Monoid α] [IsMulTorsionFree α] : IsMulTorsionFree αᵐᵒᵖ :=
⟨fun _ h => op_injective.comp (pow_left_injective h).comp unop_injective⟩

end AddOpposite
