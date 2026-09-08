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

/-!
### Additive structures on `αᵐᵒᵖ`
-/

/-
**MulOpposite.instAddSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instAddSemigroup [AddSemigroup α] : AddSemigroup αᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)

--- 原说明 ---
### Additive structures on `αᵐᵒᵖ`
-/
instance instAddSemigroup [AddSemigroup α] : AddSemigroup αᵐᵒᵖ :=
  unop_injective.addSemigroup _ fun _ _ => rfl
/-
**MulOpposite.instAddLeftCancelSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`
。
形式化陈述：instAddLeftCancelSemigroup [AddLeftCancelSemigroup α] : AddLeftCancelSemig
roup αᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
-/
instance instAddLeftCancelSemigroup [AddLeftCancelSemigroup α] : AddLeftCancelSemigroup αᵐᵒᵖ :=
  unop_injective.addLeftCancelSemigroup _ fun _ _ => rfl
/-
**MulOpposite.instAddRightCancelSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite
`。
形式化陈述：instAddRightCancelSemigroup [AddRightCancelSemigroup α] : AddRightCancelSe
migroup αᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
-/
instance instAddRightCancelSemigroup [AddRightCancelSemigroup α] : AddRightCancelSemigroup αᵐᵒᵖ :=
  unop_injective.addRightCancelSemigroup _ fun _ _ => rfl
/-
**MulOpposite.instAddCommMagma** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instAddCommMagma [AddCommMagma α] : AddCommMagma αᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
-/
instance instAddCommMagma [AddCommMagma α] : AddCommMagma αᵐᵒᵖ :=
  unop_injective.addCommMagma _ fun _ _ => rfl
/-
**MulOpposite.instAddCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instAddCommSemigroup [AddCommSemigroup α] : AddCommSemigroup αᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
-/
instance instAddCommSemigroup [AddCommSemigroup α] : AddCommSemigroup αᵐᵒᵖ :=
  unop_injective.addCommSemigroup _ fun _ _ => rfl
/-
**MulOpposite.instAddZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instAddZeroClass [AddZeroClass α] : AddZeroClass αᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
-/
instance instAddZeroClass [AddZeroClass α] : AddZeroClass αᵐᵒᵖ :=
  unop_injective.addZeroClass _ (by exact rfl) fun _ _ => rfl
/-
**MulOpposite.instAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instAddMonoid [AddMonoid α] : AddMonoid αᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
-/
instance instAddMonoid [AddMonoid α] : AddMonoid αᵐᵒᵖ :=
  unop_injective.addMonoid _ (by exact rfl) (fun _ _ => rfl) fun _ _ => rfl
/-
**MulOpposite.instAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instAddCommMonoid [AddCommMonoid α] : AddCommMonoid αᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
-/
instance instAddCommMonoid [AddCommMonoid α] : AddCommMonoid αᵐᵒᵖ :=
  unop_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
/-
**MulOpposite.instSubNegMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instSubNegMonoid [SubNegMonoid α] : SubNegMonoid αᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
-/
instance instSubNegMonoid [SubNegMonoid α] : SubNegMonoid αᵐᵒᵖ :=
  unop_injective.subNegMonoid _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
/-
**MulOpposite.instAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instAddGroup [AddGroup α] : AddGroup αᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
-/
instance instAddGroup [AddGroup α] : AddGroup αᵐᵒᵖ :=
  unop_injective.addGroup _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
  (fun _ _ => rfl) fun _ _ => rfl
/-
**MulOpposite.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instAddCommGroup [AddCommGroup α] : AddCommGroup αᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
-/
instance instAddCommGroup [AddCommGroup α] : AddCommGroup αᵐᵒᵖ :=
  unop_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

/-!
### Multiplicative structures on `αᵐᵒᵖ`

We also generate additive structures on `αᵃᵒᵖ` using `to_additive`
-/

@[to_additive]
/-
**MulOpposite.instIsRightCancelMul** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instIsRightCancelMul [Mul α] [IsLeftCancelMul α] : IsRightCancelMul αᵐᵒᵖ w
here mul_right_cancel _ _ _ h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
· 使用定理 `mul_left_cancel`：mul_left_cancel : a * b = a * c -> b = c
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)

--- 原说明 ---
### Multiplicative structures on `αᵐᵒᵖ`

We also generate additive structures on `αᵃᵒᵖ` using `to_additive`
-/
instance instIsRightCancelMul [Mul α] [IsLeftCancelMul α] : IsRightCancelMul αᵐᵒᵖ where
  mul_right_cancel _ _ _ h := unop_injective <| mul_left_cancel <| op_injective h

@[to_additive]
/-
**MulOpposite.instIsLeftCancelMul** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instIsLeftCancelMul [Mul α] [IsRightCancelMul α] : IsLeftCancelMul αᵐᵒᵖ wh
ere mul_left_cancel _ _ _ h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
· 使用定理 `mul_right_cancel`：mul_right_cancel : a * b = c * b -> a = c
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
-/
instance instIsLeftCancelMul [Mul α] [IsRightCancelMul α] : IsLeftCancelMul αᵐᵒᵖ where
  mul_left_cancel _ _ _ h := unop_injective <| mul_right_cancel <| op_injective h
/-
**MulOpposite.instIsCancelMul** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Mul α] [IsCancelMul α], IsCancelMul αᵐᵒᵖ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCancelMul.toIsRightCancelMul`：∀ {G : Type u} {inst : Mul G} [self : Is
CancelMul G], IsRightCancelMul G
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
-/
@[to_additive] instance instIsCancelMul [Mul α] [IsCancelMul α] : IsCancelMul αᵐᵒᵖ where

@[to_additive]
/-
**MulOpposite.instSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instSemigroup [Semigroup α] : Semigroup αᵐᵒᵖ where mul_assoc x y z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemigroup [Semigroup α] : Semigroup αᵐᵒᵖ where
  mul_assoc x y z := unop_injective <| Eq.symm <| mul_assoc (unop z) (unop y) (unop x)

@[to_additive]
/-
**MulOpposite.instLeftCancelSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instLeftCancelSemigroup [RightCancelSemigroup α] : LeftCancelSemigroup αᵐᵒ
ᵖ where mul_left_cancel _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLeftCancelSemigroup [RightCancelSemigroup α] : LeftCancelSemigroup αᵐᵒᵖ where
  mul_left_cancel _ _ _ := mul_left_cancel

@[to_additive]
/-
**MulOpposite.instRightCancelSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instRightCancelSemigroup [LeftCancelSemigroup α] : RightCancelSemigroup αᵐ
ᵒᵖ where mul_right_cancel _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRightCancelSemigroup [LeftCancelSemigroup α] : RightCancelSemigroup αᵐᵒᵖ where
  mul_right_cancel _ _ _ := mul_right_cancel

@[to_additive]
/-
**MulOpposite.instCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instCommSemigroup [CommSemigroup α] : CommSemigroup αᵐᵒᵖ where mul_comm x 
y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommSemigroup [CommSemigroup α] : CommSemigroup αᵐᵒᵖ where
  mul_comm x y := unop_injective <| mul_comm (unop y) (unop x)
/-
**MulOpposite.instMulOne** 是 Mathlib 中的一个定义，位于命名空间 `MulOpposite`。
形式化陈述：{α : Type u_1} → [MulOne α] → MulOne αᵐᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance instMulOne [MulOne α] : MulOne αᵐᵒᵖ where

@[to_additive]
/-
**MulOpposite.instMulOneClass** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instMulOneClass [MulOneClass α] : MulOneClass αᵐᵒᵖ where one_mul _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulOneClass [MulOneClass α] : MulOneClass αᵐᵒᵖ where
  one_mul _ := unop_injective <| mul_one _
  mul_one _ := unop_injective <| one_mul _

@[to_additive]
/-
**MulOpposite.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instMonoid [Monoid α] : Monoid αᵐᵒᵖ where toSemigroup
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoid [Monoid α] : Monoid αᵐᵒᵖ where
  toSemigroup := instSemigroup
  __ := instMulOneClass
  npow n a := op <| a.unop ^ n
  npow_zero _ := unop_injective <| pow_zero _
  npow_succ _ _ := unop_injective <| pow_succ' _ _

@[to_additive]
/-
**MulOpposite.instLeftCancelMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instLeftCancelMonoid [RightCancelMonoid α] : LeftCancelMonoid αᵐᵒᵖ where t
oMonoid
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLeftCancelMonoid [RightCancelMonoid α] : LeftCancelMonoid αᵐᵒᵖ where
  toMonoid := instMonoid
  __ := instLeftCancelSemigroup

@[to_additive]
/-
**MulOpposite.instRightCancelMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instRightCancelMonoid [LeftCancelMonoid α] : RightCancelMonoid αᵐᵒᵖ where 
toMonoid
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRightCancelMonoid [LeftCancelMonoid α] : RightCancelMonoid αᵐᵒᵖ where
  toMonoid := instMonoid
  __ := instRightCancelSemigroup

@[to_additive]
/-
**MulOpposite.instCancelMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instCancelMonoid [CancelMonoid α] : CancelMonoid αᵐᵒᵖ where toLeftCancelMo
noid
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCancelMonoid [CancelMonoid α] : CancelMonoid αᵐᵒᵖ where
  toLeftCancelMonoid := instLeftCancelMonoid
  __ := instRightCancelMonoid

@[to_additive]
/-
**MulOpposite.instCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instCommMonoid [CommMonoid α] : CommMonoid αᵐᵒᵖ where toMonoid
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommMonoid [CommMonoid α] : CommMonoid αᵐᵒᵖ where
  toMonoid := instMonoid
  __ := instCommSemigroup

@[to_additive]
/-
**MulOpposite.instCancelCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instCancelCommMonoid [CancelCommMonoid α] : CancelCommMonoid αᵐᵒᵖ where to
CommMonoid
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCancelCommMonoid [CancelCommMonoid α] : CancelCommMonoid αᵐᵒᵖ where
  toCommMonoid := instCommMonoid
  __ := instLeftCancelMonoid

@[to_additive AddOpposite.instSubNegMonoid]
/-
**MulOpposite.instDivInvMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instDivInvMonoid [DivInvMonoid α] : DivInvMonoid αᵐᵒᵖ where toMonoid
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDivInvMonoid [DivInvMonoid α] : DivInvMonoid αᵐᵒᵖ where
  toMonoid := instMonoid
  toInv := instInv
  zpow n a := op <| a.unop ^ n
  zpow_zero' _ := unop_injective <| zpow_zero _
  zpow_succ' _ _ := unop_injective <| by
    simp_rw [HPow.hPow, Pow.pow]
    rw [unop_op, zpow_natCast, pow_succ', unop_mul, unop_op, zpow_natCast]
  zpow_neg' _ _ := unop_injective <| DivInvMonoid.zpow_neg' _ _

@[to_additive]
/-
**MulOpposite.instDivisionMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instDivisionMonoid [DivisionMonoid α] : DivisionMonoid αᵐᵒᵖ where toDivInv
Monoid
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDivisionMonoid [DivisionMonoid α] : DivisionMonoid αᵐᵒᵖ where
  toDivInvMonoid := instDivInvMonoid
  __ := instInvolutiveInv
  mul_inv_rev _ _ := unop_injective <| mul_inv_rev _ _
  inv_eq_of_mul _ _ h := unop_injective <| inv_eq_of_mul_eq_one_left <| congr_arg unop h

@[to_additive AddOpposite.instSubtractionCommMonoid]
/-
**MulOpposite.instDivisionCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instDivisionCommMonoid [DivisionCommMonoid α] : DivisionCommMonoid αᵐᵒᵖ wh
ere toDivisionMonoid
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDivisionCommMonoid [DivisionCommMonoid α] : DivisionCommMonoid αᵐᵒᵖ where
  toDivisionMonoid := instDivisionMonoid
  __ := instCommSemigroup

@[to_additive]
/-
**MulOpposite.instGroup** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instGroup [Group α] : Group αᵐᵒᵖ where toDivInvMonoid
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instGroup [Group α] : Group αᵐᵒᵖ where
  toDivInvMonoid := instDivInvMonoid
  inv_mul_cancel _ := unop_injective <| mul_inv_cancel _

@[to_additive]
/-
**MulOpposite.instCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instCommGroup [CommGroup α] : CommGroup αᵐᵒᵖ where toGroup
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommGroup [CommGroup α] : CommGroup αᵐᵒᵖ where
  toGroup := instGroup
  __ := instCommSemigroup

section Monoid
variable [Monoid α]

/-
**MulOpposite.op_pow** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Monoid α] (x : α) (n : ℕ), MulOpposite.op (x ^ n)
 = MulOpposite.op x ^ n
参数：x : α；n : ℕ；x ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma op_pow (x : α) (n : ℕ) : op (x ^ n) = op x ^ n := rfl
/-
**MulOpposite.unop_pow** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Monoid α] (x : αᵐᵒᵖ) (n : ℕ), MulOpposite.unop (x
 ^ n) = MulOpposite.unop x ^ n
参数：x : αᵐᵒᵖ；n : ℕ；x ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma unop_pow (x : αᵐᵒᵖ) (n : ℕ) : unop (x ^ n) = unop x ^ n := rfl

end Monoid

section DivInvMonoid
variable [DivInvMonoid α]

/-
**MulOpposite.op_zpow** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : DivInvMonoid α] (x : α) (z : ℤ), MulOpposite.op (
x ^ z) = MulOpposite.op x ^ z
参数：x : α；z : ℤ；x ^ z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma op_zpow (x : α) (z : ℤ) : op (x ^ z) = op x ^ z := rfl
/-
**MulOpposite.unop_zpow** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : DivInvMonoid α] (x : αᵐᵒᵖ) (z : ℤ), MulOpposite.u
nop (x ^ z) = MulOpposite.unop x ^ z
参数：x : αᵐᵒᵖ；z : ℤ；x ^ z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma unop_zpow (x : αᵐᵒᵖ) (z : ℤ) : unop (x ^ z) = unop x ^ z := rfl

end DivInvMonoid

@[to_additive (attr := simp)]
/-
**MulOpposite.unop_div** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：unop_div [DivInvMonoid α] (x y : αᵐᵒᵖ) : unop (x / y) = (unop y)⁻¹ * unop 
x
参数：x y : αᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_div [DivInvMonoid α] (x y : αᵐᵒᵖ) : unop (x / y) = (unop y)⁻¹ * unop x :=
  rfl

@[to_additive (attr := simp)]
/-
**MulOpposite.op_div** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：op_div [DivInvMonoid α] (x y : α) : op (x / y) = (op y)⁻¹ * op x
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem op_div [DivInvMonoid α] (x y : α) : op (x / y) = (op y)⁻¹ * op x := by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/-
**MulOpposite.semiconjBy_op** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：semiconjBy_op [Mul α] {a x y : α} : SemiconjBy (op a) (op y) (op x) ↔ Semi
conjBy a x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem semiconjBy_op [Mul α] {a x y : α} : SemiconjBy (op a) (op y) (op x) ↔ SemiconjBy a x y := by
  simp only [SemiconjBy, ← op_mul, op_inj, eq_comm]

@[to_additive (attr := simp, nolint simpComm)]
/-
**MulOpposite.semiconjBy_unop** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：semiconjBy_unop [Mul α] {a x y : αᵐᵒᵖ} : SemiconjBy (unop a) (unop y) (uno
p x) ↔ SemiconjBy a x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulOpposite.op_unop`：op_unop (x : αᵐᵒᵖ) : op (unop x) = x
· 使用定理 `MulOpposite.semiconjBy_op`：semiconjBy_op [Mul α] {a x y : α} : SemiconjB
y (op a) (op y) (op x) ↔ SemiconjBy a x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem semiconjBy_unop [Mul α] {a x y : αᵐᵒᵖ} :
    SemiconjBy (unop a) (unop y) (unop x) ↔ SemiconjBy a x y := by
  conv_rhs => rw [← op_unop a, ← op_unop x, ← op_unop y, semiconjBy_op]

attribute [nolint simpComm] AddOpposite.addSemiconjBy_unop

@[to_additive]
/-
**MulOpposite._root_.SemiconjBy.op** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.SemiconjBy.op [Mul α] {a x y : α} (h : SemiconjBy a x y) :
    SemiconjBy (op a) (op y) (op x) :=
  semiconjBy_op.2 h

@[to_additive]
/-
**MulOpposite._root_.SemiconjBy.unop** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.SemiconjBy.unop [Mul α] {a x y : αᵐᵒᵖ} (h : SemiconjBy a x y) :
    SemiconjBy (unop a) (unop y) (unop x) :=
  semiconjBy_unop.2 h

@[to_additive]
/-
**MulOpposite._root_.Commute.op** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Commute.op [Mul α] {x y : α} (h : Commute x y) : Commute (op x) (op y) :=
  SemiconjBy.op h

@[to_additive]
nonrec theorem _root_.Commute.unop [Mul α] {x y : αᵐᵒᵖ} (h : Commute x y) :
    Commute (unop x) (unop y) :=
  h.unop

@[to_additive (attr := simp)]
/-
**MulOpposite.commute_op** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：commute_op [Mul α] {x y : α} : Commute (op x) (op y) ↔ Commute x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.semiconjBy_op`：semiconjBy_op [Mul α] {a x y : α} : SemiconjB
y (op a) (op y) (op x) ↔ SemiconjBy a x y
-/
theorem commute_op [Mul α] {x y : α} : Commute (op x) (op y) ↔ Commute x y :=
  semiconjBy_op

@[to_additive (attr := simp, nolint simpComm)]
/-
**MulOpposite.commute_unop** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：commute_unop [Mul α] {x y : αᵐᵒᵖ} : Commute (unop x) (unop y) ↔ Commute x 
y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.semiconjBy_unop`：semiconjBy_unop [Mul α] {a x y : αᵐᵒᵖ} : Se
miconjBy (unop a) (unop y) (unop x) ↔ SemiconjBy a x y
-/
theorem commute_unop [Mul α] {x y : αᵐᵒᵖ} : Commute (unop x) (unop y) ↔ Commute x y :=
  semiconjBy_unop

attribute [nolint simpComm] AddOpposite.addCommute_unop
/-
**MulOpposite.isDedekindFiniteMonoid_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`
。
形式化陈述：∀ {α : Type u_1} [inst : MulOne α], IsDedekindFiniteMonoid αᵐᵒᵖ ↔ IsDedeki
ndFiniteMonoid α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.forall_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e 
: α ≃ β), (∀ (a : α), q (e a)) ↔ ∀ (b : β), q b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MulOpposite.opEquiv_apply`：∀ {α : Type u_1}, ⇑MulOpposite.opEquiv = MulO
pposite.op
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
@[to_additive] protected theorem isDedekindFiniteMonoid_iff [MulOne α] :
    IsDedekindFiniteMonoid αᵐᵒᵖ ↔ IsDedekindFiniteMonoid α := by
  simp_rw [isDedekindFiniteMonoid_iff, ← opEquiv.forall_congr_right]
  simpa [← op_one, ← op_mul] using forall_comm
/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [MulOne α] [IsDedekindFiniteMonoid α] : IsDedekindFiniteMonoid αᵐᵒᵖ :=
  MulOpposite.isDedekindFiniteMonoid_iff.mpr ‹_›

end MulOpposite

/-!
### Multiplicative structures on `αᵃᵒᵖ`
-/


namespace AddOpposite

/-
**AddOpposite.instSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instSemigroup [Semigroup α] : Semigroup αᵃᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddOpposite.unop_injective`：∀ {α : Type u_1}, Function.Injective AddOppo
site.unop
-/
instance instSemigroup [Semigroup α] : Semigroup αᵃᵒᵖ := unop_injective.semigroup _ fun _ _ ↦ rfl
/-
**AddOpposite.instLeftCancelSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instLeftCancelSemigroup [LeftCancelSemigroup α] : LeftCancelSemigroup αᵃᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddOpposite.unop_injective`：∀ {α : Type u_1}, Function.Injective AddOppo
site.unop
-/
instance instLeftCancelSemigroup [LeftCancelSemigroup α] : LeftCancelSemigroup αᵃᵒᵖ :=
  unop_injective.leftCancelSemigroup _ fun _ _ => rfl
/-
**AddOpposite.instRightCancelSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instRightCancelSemigroup [RightCancelSemigroup α] : RightCancelSemigroup α
ᵃᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddOpposite.unop_injective`：∀ {α : Type u_1}, Function.Injective AddOppo
site.unop
-/
instance instRightCancelSemigroup [RightCancelSemigroup α] : RightCancelSemigroup αᵃᵒᵖ :=
  unop_injective.rightCancelSemigroup _ fun _ _ => rfl
/-
**AddOpposite.instCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instCommSemigroup [CommSemigroup α] : CommSemigroup αᵃᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddOpposite.unop_injective`：∀ {α : Type u_1}, Function.Injective AddOppo
site.unop
-/
instance instCommSemigroup [CommSemigroup α] : CommSemigroup αᵃᵒᵖ :=
  unop_injective.commSemigroup _ fun _ _ => rfl
/-
**AddOpposite.instMulOneClass** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instMulOneClass [MulOneClass α] : MulOneClass αᵃᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddOpposite.unop_injective`：∀ {α : Type u_1}, Function.Injective AddOppo
site.unop
-/
instance instMulOneClass [MulOneClass α] : MulOneClass αᵃᵒᵖ :=
  unop_injective.mulOneClass _ (by exact rfl) fun _ _ => rfl
/-
**AddOpposite.pow** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：pow {β} [Pow α β] : Pow αᵃᵒᵖ β where pow a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance pow {β} [Pow α β] : Pow αᵃᵒᵖ β where pow a b := op (unop a ^ b)

@[simp]
/-
**AddOpposite.op_pow** 是 Mathlib 中的一个定理，位于命名空间 `AddOpposite`。
形式化陈述：op_pow {β} [Pow α β] (a : α) (b : β) : op (a ^ b) = op a ^ b
参数：a : α；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_pow {β} [Pow α β] (a : α) (b : β) : op (a ^ b) = op a ^ b :=
  rfl

@[simp]
/-
**AddOpposite.unop_pow** 是 Mathlib 中的一个定理，位于命名空间 `AddOpposite`。
形式化陈述：unop_pow {β} [Pow α β] (a : αᵃᵒᵖ) (b : β) : unop (a ^ b) = unop a ^ b
参数：a : αᵃᵒᵖ；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_pow {β} [Pow α β] (a : αᵃᵒᵖ) (b : β) : unop (a ^ b) = unop a ^ b :=
  rfl
/-
**AddOpposite.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instMonoid [Monoid α] : Monoid αᵃᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddOpposite.unop_injective`：∀ {α : Type u_1}, Function.Injective AddOppo
site.unop
-/
instance instMonoid [Monoid α] : Monoid αᵃᵒᵖ :=
  unop_injective.monoid _ (by exact rfl) (fun _ _ => rfl) fun _ _ => rfl
/-
**AddOpposite.instCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instCommMonoid [CommMonoid α] : CommMonoid αᵃᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddOpposite.unop_injective`：∀ {α : Type u_1}, Function.Injective AddOppo
site.unop
-/
instance instCommMonoid [CommMonoid α] : CommMonoid αᵃᵒᵖ :=
  unop_injective.commMonoid _ (by exact rfl) (fun _ _ => rfl) fun _ _ => rfl
/-
**AddOpposite.instDivInvMonoid** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instDivInvMonoid [DivInvMonoid α] : DivInvMonoid αᵃᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddOpposite.unop_injective`：∀ {α : Type u_1}, Function.Injective AddOppo
site.unop
-/
instance instDivInvMonoid [DivInvMonoid α] : DivInvMonoid αᵃᵒᵖ :=
  unop_injective.divInvMonoid _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
/-
**AddOpposite.instGroup** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instGroup [Group α] : Group αᵃᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddOpposite.unop_injective`：∀ {α : Type u_1}, Function.Injective AddOppo
site.unop
-/
instance instGroup [Group α] : Group αᵃᵒᵖ :=
  unop_injective.group _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
/-
**AddOpposite.instCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instCommGroup [CommGroup α] : CommGroup αᵃᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddOpposite.unop_injective`：∀ {α : Type u_1}, Function.Injective AddOppo
site.unop
-/
instance instCommGroup [CommGroup α] : CommGroup αᵃᵒᵖ :=
  unop_injective.commGroup _ (by exact rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
/-
**AddOpposite.instMulTorsionFree** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instMulTorsionFree [Monoid α] [IsMulTorsionFree α] : IsMulTorsionFree αᵐᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `AddOpposite.op_injective`：∀ {α : Type u_1}, Function.Injective AddOpposi
te.op
· 使用引理 `pow_left_injective`：pow_left_injective (hn : n != 0) : Injective fun a :
 M => a ^ n
· 使用定理 `AddOpposite.unop_injective`：∀ {α : Type u_1}, Function.Injective AddOppo
site.unop
-/
instance instMulTorsionFree [Monoid α] [IsMulTorsionFree α] : IsMulTorsionFree αᵐᵒᵖ :=
  ⟨fun _ h ↦ op_injective.comp <| (pow_left_injective h).comp <| unop_injective⟩

end AddOpposite

