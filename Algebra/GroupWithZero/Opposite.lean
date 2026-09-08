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

/-
**MulOpposite.instMulZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instMulZeroClass [MulZeroClass α] : MulZeroClass αᵐᵒᵖ where zero_mul _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulZeroClass [MulZeroClass α] : MulZeroClass αᵐᵒᵖ where
  zero_mul _ := unop_injective <| mul_zero _
  mul_zero _ := unop_injective <| zero_mul _
/-
**MulOpposite.instMulZeroOneClass** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instMulZeroOneClass [MulZeroOneClass α] : MulZeroOneClass αᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulZeroOneClass [MulZeroOneClass α] : MulZeroOneClass αᵐᵒᵖ where
  __ := instMulOneClass
  __ := instMulZeroClass
/-
**MulOpposite.instSemigroupWithZero** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instSemigroupWithZero [SemigroupWithZero α] : SemigroupWithZero αᵐᵒᵖ where
 __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemigroupWithZero [SemigroupWithZero α] : SemigroupWithZero αᵐᵒᵖ where
  __ := instSemigroup
  __ := instMulZeroClass
/-
**MulOpposite.instMonoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instMonoidWithZero [MonoidWithZero α] : MonoidWithZero αᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoidWithZero [MonoidWithZero α] : MonoidWithZero αᵐᵒᵖ where
  __ := instMonoid
  __ := instMulZeroOneClass
/-
**MulOpposite.instGroupWithZero** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instGroupWithZero [GroupWithZero α] : GroupWithZero αᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instGroupWithZero [GroupWithZero α] : GroupWithZero αᵐᵒᵖ where
  __ := instMonoidWithZero
  __ := instNontrivial
  __ := instDivInvMonoid
  mul_inv_cancel _ hx := unop_injective <| inv_mul_cancel₀ <| unop_injective.ne hx
  inv_zero := unop_injective inv_zero
/-
**MulOpposite.instNoZeroDivisors** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instNoZeroDivisors [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors αᵐ
ᵒᵖ where eq_zero_or_eq_zero_of_mul_eq_zero (H : op (_ * _) = op (0 : α))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero`：∀ {M₀ : Type u_2} {ins
t : Mul M₀} {inst_1 : Zero M₀} [self : NoZeroDivisors M₀] {a b : M₀}, a * b = 0 
→ a = 0 ∨ b = 0
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
-/
instance instNoZeroDivisors [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors αᵐᵒᵖ where
  eq_zero_or_eq_zero_of_mul_eq_zero (H : op (_ * _) = op (0 : α)) :=
      Or.casesOn (eq_zero_or_eq_zero_of_mul_eq_zero <| op_injective H)
        (fun hy => Or.inr <| unop_injective <| hy) fun hx => Or.inl <| unop_injective <| hx
/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul α] [Zero α] [IsLeftCancelMulZero α] : IsRightCancelMulZero αᵐᵒᵖ where
  mul_right_cancel_of_ne_zero h _ _ eq := unop_injective <|
    mul_left_cancel₀ (unop_injective.ne_iff.mpr h) (congr_arg unop eq)
/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul α] [Zero α] [IsRightCancelMulZero α] : IsLeftCancelMulZero αᵐᵒᵖ where
  mul_left_cancel_of_ne_zero h _ _ eq := unop_injective <|
    mul_right_cancel₀ (unop_injective.ne_iff.mpr h) (congr_arg unop eq)
/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul α] [Zero α] [IsCancelMulZero α] : IsCancelMulZero αᵐᵒᵖ where
/-
**MulOpposite.isLeftCancelMulZero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α], IsLeftCancelMulZero αᵐᵒ
ᵖ ↔ IsRightCancelMulZero α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isRightCancelMulZero`：∀ {M₀ : Type u_1} {M₀' : Type u
_3} [inst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   
(f : M₀ → M₀'),   Function.In…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `MulOpposite.instIsRightCancelMulZeroOfIsLeftCancelMulZero`：∀ {α : Type u
_1} [inst : Mul α] [inst_1 : Zero α] [IsLeftCancelMulZero α], IsRightCancelMulZe
ro αᵐᵒᵖ
· 使用定理 `MulOpposite.instIsLeftCancelMulZeroOfIsRightCancelMulZero`：∀ {α : Type u
_1} [inst : Mul α] [inst_1 : Zero α] [IsRightCancelMulZero α], IsLeftCancelMulZe
ro αᵐᵒᵖ
-/
@[simp] theorem isLeftCancelMulZero_iff [Mul α] [Zero α] :
    IsLeftCancelMulZero αᵐᵒᵖ ↔ IsRightCancelMulZero α where
  mp _ := (op_injective.comp op_injective).isRightCancelMulZero _ rfl fun _ _ ↦ rfl
  mpr _ := inferInstance
/-
**MulOpposite.isRightCancelMulZero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α], IsRightCancelMulZero αᵐ
ᵒᵖ ↔ IsLeftCancelMulZero α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isLeftCancelMulZero`：∀ {M₀ : Type u_1} {M₀' : Type u_
3} [inst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   (
f : M₀ → M₀'),   Function.In…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `MulOpposite.instIsLeftCancelMulZeroOfIsRightCancelMulZero`：∀ {α : Type u
_1} [inst : Mul α] [inst_1 : Zero α] [IsRightCancelMulZero α], IsLeftCancelMulZe
ro αᵐᵒᵖ
· 使用定理 `MulOpposite.instIsRightCancelMulZeroOfIsLeftCancelMulZero`：∀ {α : Type u
_1} [inst : Mul α] [inst_1 : Zero α] [IsLeftCancelMulZero α], IsRightCancelMulZe
ro αᵐᵒᵖ
-/
@[simp] theorem isRightCancelMulZero_iff [Mul α] [Zero α] :
    IsRightCancelMulZero αᵐᵒᵖ ↔ IsLeftCancelMulZero α where
  mp _ := (op_injective.comp op_injective).isLeftCancelMulZero _ rfl fun _ _ ↦ rfl
  mpr _ := inferInstance
/-
**MulOpposite.isCancelMulZero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α], IsCancelMulZero αᵐᵒᵖ ↔ 
IsCancelMulZero α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isCancelMulZero`：∀ {M₀ : Type u_1} {M₀' : Type u_3} [
inst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   (f : 
M₀ → M₀'),   Function.In…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `MulOpposite.op_injective`：op_injective : Injective (op : α -> αᵐᵒᵖ)
· 使用定理 `MulOpposite.instIsCancelMulZero`：∀ {α : Type u_1} [inst : Mul α] [inst_1
 : Zero α] [IsCancelMulZero α], IsCancelMulZero αᵐᵒᵖ
-/
@[simp] theorem isCancelMulZero_iff [Mul α] [Zero α] :
    IsCancelMulZero αᵐᵒᵖ ↔ IsCancelMulZero α where
  mp _ := (op_injective.comp op_injective).isCancelMulZero _ rfl fun _ _ ↦ rfl
  mpr _ := inferInstance

end MulOpposite

namespace AddOpposite

/-
**AddOpposite.instMulZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instMulZeroClass [MulZeroClass α] : MulZeroClass αᵃᵒᵖ where zero_mul _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulZeroClass [MulZeroClass α] : MulZeroClass αᵃᵒᵖ where
  zero_mul _ := unop_injective <| zero_mul _
  mul_zero _ := unop_injective <| mul_zero _
/-
**AddOpposite.instMulZeroOneClass** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instMulZeroOneClass [MulZeroOneClass α] : MulZeroOneClass αᵃᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulZeroOneClass [MulZeroOneClass α] : MulZeroOneClass αᵃᵒᵖ where
  __ := instMulOneClass
  __ := instMulZeroClass
/-
**AddOpposite.instSemigroupWithZero** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instSemigroupWithZero [SemigroupWithZero α] : SemigroupWithZero αᵃᵒᵖ where
 __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemigroupWithZero [SemigroupWithZero α] : SemigroupWithZero αᵃᵒᵖ where
  __ := instSemigroup
  __ := instMulZeroClass
/-
**AddOpposite.instMonoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instMonoidWithZero [MonoidWithZero α] : MonoidWithZero αᵃᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoidWithZero [MonoidWithZero α] : MonoidWithZero αᵃᵒᵖ where
  __ := instMonoid
  __ := instMulZeroOneClass
/-
**AddOpposite.instNoZeroDivisors** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instNoZeroDivisors [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors αᵃ
ᵒᵖ where eq_zero_or_eq_zero_of_mul_eq_zero (H : op (_ * _) = op (0 : α))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `AddOpposite.unop_injective`：∀ {α : Type u_1}, Function.Injective AddOppo
site.unop
· 使用定理 `NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero`：∀ {M₀ : Type u_2} {ins
t : Mul M₀} {inst_1 : Zero M₀} [self : NoZeroDivisors M₀] {a b : M₀}, a * b = 0 
→ a = 0 ∨ b = 0
· 使用定理 `AddOpposite.op_injective`：∀ {α : Type u_1}, Function.Injective AddOpposi
te.op
-/
instance instNoZeroDivisors [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors αᵃᵒᵖ where
  eq_zero_or_eq_zero_of_mul_eq_zero (H : op (_ * _) = op (0 : α)) :=
    Or.imp (fun hx => unop_injective hx) (fun hy => unop_injective hy)
    (@eq_zero_or_eq_zero_of_mul_eq_zero α _ _ _ _ _ <| op_injective H)
/-
**AddOpposite.instGroupWithZero** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
形式化陈述：instGroupWithZero [GroupWithZero α] : GroupWithZero αᵃᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instGroupWithZero [GroupWithZero α] : GroupWithZero αᵃᵒᵖ where
  __ := instMonoidWithZero
  __ := instNontrivial
  __ := instDivInvMonoid
  mul_inv_cancel _ hx := unop_injective <| mul_inv_cancel₀ <| unop_injective.ne hx
  inv_zero := unop_injective inv_zero

end AddOpposite

