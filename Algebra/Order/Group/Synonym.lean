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
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [One α] : One αᵒᵈ := inferInstanceAs <| One α

set_option backward.inferInstanceAs.wrap.instances false in
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Mul α] : Mul αᵒᵈ := inferInstanceAs <| Mul α

set_option backward.inferInstanceAs.wrap.instances false in
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Inv α] : Inv αᵒᵈ := inferInstanceAs <| Inv α

set_option backward.inferInstanceAs.wrap.instances false in
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Div α] : Div αᵒᵈ := inferInstanceAs <| Div α

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive (attr := to_additive) (reorder := 1 2) OrderDual.instSMul]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Pow α β] : Pow αᵒᵈ β := inferInstanceAs <| Pow α β

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive (attr := to_additive) (reorder := 1 2) OrderDual.instSMul']
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Pow α β] : Pow α βᵒᵈ := inferInstanceAs <| Pow α β
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Semigroup α] : Semigroup αᵒᵈ := inferInstanceAs <| Semigroup α
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [CommSemigroup α] : CommSemigroup αᵒᵈ := inferInstanceAs <| CommSemigroup α

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul α] [IsLeftCancelMul α] : IsLeftCancelMul αᵒᵈ :=
  inferInstanceAs <| IsLeftCancelMul α

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul α] [IsRightCancelMul α] : IsRightCancelMul αᵒᵈ :=
  inferInstanceAs <| IsRightCancelMul α

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul α] [IsCancelMul α] : IsCancelMul αᵒᵈ where

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LeftCancelSemigroup α] : LeftCancelSemigroup αᵒᵈ where

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [RightCancelSemigroup α] : RightCancelSemigroup αᵒᵈ where

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulOneClass α] : MulOneClass αᵒᵈ := inferInstanceAs <| MulOneClass α

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid α] : Monoid αᵒᵈ := inferInstanceAs <| Monoid α

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommMonoid α] : CommMonoid αᵒᵈ := inferInstanceAs <| CommMonoid α

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LeftCancelMonoid α] : LeftCancelMonoid αᵒᵈ := inferInstanceAs <| LeftCancelMonoid α

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [RightCancelMonoid α] : RightCancelMonoid αᵒᵈ := inferInstanceAs <| RightCancelMonoid α

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CancelMonoid α] : CancelMonoid αᵒᵈ := inferInstanceAs <| CancelMonoid α

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CancelCommMonoid α] : CancelCommMonoid αᵒᵈ := inferInstanceAs <| CancelCommMonoid α

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [InvolutiveInv α] : InvolutiveInv αᵒᵈ := inferInstanceAs <| InvolutiveInv α

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DivInvMonoid α] : DivInvMonoid αᵒᵈ := inferInstanceAs <| DivInvMonoid α

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DivisionMonoid α] : DivisionMonoid αᵒᵈ := inferInstanceAs <| DivisionMonoid α

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DivisionCommMonoid α] : DivisionCommMonoid αᵒᵈ :=
  inferInstanceAs <| DivisionCommMonoid α

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Group α] : Group αᵒᵈ := inferInstanceAs <| Group α

@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommGroup α] : CommGroup αᵒᵈ := inferInstanceAs <| CommGroup α

end OrderDual

@[to_additive (attr := simp)]
/-
**toDual_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toDual_one [One α] : toDual (1 : α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDual_one [One α] : toDual (1 : α) = 1 := rfl

@[to_additive (attr := simp)]
/-
**ofDual_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDual_one [One α] : (ofDual 1 : α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofDual_one [One α] : (ofDual 1 : α) = 1 := rfl
/-
**toDual_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : One α] {a : α}, OrderDual.toDual a = 1 ↔ a = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive (attr := simp)] lemma toDual_eq_one [One α] {a : α} : toDual a = 1 ↔ a = 1 := .rfl
/-
**ofDual_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : One α] {a : αᵒᵈ}, OrderDual.ofDual a = 1 ↔ a = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive (attr := simp)] lemma ofDual_eq_one [One α] {a : αᵒᵈ} : ofDual a = 1 ↔ a = 1 := .rfl

@[to_additive (attr := simp)]
/-
**toDual_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toDual_mul [Mul α] (a b : α) : toDual (a * b) = toDual a * toDual b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDual_mul [Mul α] (a b : α) : toDual (a * b) = toDual a * toDual b := rfl

@[to_additive (attr := simp)]
/-
**ofDual_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDual_mul [Mul α] (a b : αᵒᵈ) : ofDual (a * b) = ofDual a * ofDual b
参数：a b : αᵒᵈ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofDual_mul [Mul α] (a b : αᵒᵈ) : ofDual (a * b) = ofDual a * ofDual b := rfl

@[to_additive (attr := simp)]
/-
**toDual_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toDual_inv [Inv α] (a : α) : toDual a⁻¹ = (toDual a)⁻¹
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDual_inv [Inv α] (a : α) : toDual a⁻¹ = (toDual a)⁻¹ := rfl

@[to_additive (attr := simp)]
/-
**ofDual_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDual_inv [Inv α] (a : αᵒᵈ) : ofDual a⁻¹ = (ofDual a)⁻¹
参数：a : αᵒᵈ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofDual_inv [Inv α] (a : αᵒᵈ) : ofDual a⁻¹ = (ofDual a)⁻¹ := rfl

@[to_additive (attr := simp)]
/-
**toDual_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toDual_div [Div α] (a b : α) : toDual (a / b) = toDual a / toDual b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDual_div [Div α] (a b : α) : toDual (a / b) = toDual a / toDual b := rfl

@[to_additive (attr := simp)]
/-
**ofDual_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDual_div [Div α] (a b : αᵒᵈ) : ofDual (a / b) = ofDual a / ofDual b
参数：a b : αᵒᵈ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofDual_div [Div α] (a b : αᵒᵈ) : ofDual (a / b) = ofDual a / ofDual b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toDual_smul]
/-
**toDual_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toDual_pow [Pow α β] (a : α) (b : β) : toDual (a ^ b) = toDual a ^ b
参数：a : α；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDual_pow [Pow α β] (a : α) (b : β) : toDual (a ^ b) = toDual a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofDual_smul]
/-
**ofDual_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDual_pow [Pow α β] (a : αᵒᵈ) (b : β) : ofDual (a ^ b) = ofDual a ^ b
参数：a : αᵒᵈ；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofDual_pow [Pow α β] (a : αᵒᵈ) (b : β) : ofDual (a ^ b) = ofDual a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toDual_smul']
/-
**pow_toDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_toDual [Pow α β] (a : α) (b : β) : a ^ toDual b = a ^ b
参数：a : α；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_toDual [Pow α β] (a : α) (b : β) : a ^ toDual b = a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofDual_smul']
/-
**pow_ofDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_ofDual [Pow α β] (a : α) (b : βᵒᵈ) : a ^ ofDual b = a ^ b
参数：a : α；b : βᵒᵈ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_ofDual [Pow α β] (a : α) (b : βᵒᵈ) : a ^ ofDual b = a ^ b := rfl

section Monoid
variable [Monoid α]

@[to_additive (attr := simp)]
/-
**isLeftRegular_toDual** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLeftRegular_toDual {a : α} : IsLeftRegular (toDual a) ↔ IsLeftRegular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLeftRegular_toDual {a : α} : IsLeftRegular (toDual a) ↔ IsLeftRegular a := .rfl

@[to_additive (attr := simp)]
/-
**isLeftRegular_ofDual** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLeftRegular_ofDual {a : αᵒᵈ} : IsLeftRegular (ofDual a) ↔ IsLeftRegular 
a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLeftRegular_ofDual {a : αᵒᵈ} : IsLeftRegular (ofDual a) ↔ IsLeftRegular a := .rfl

@[to_additive (attr := simp)]
/-
**isRightRegular_toDual** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isRightRegular_toDual {a : α} : IsRightRegular (toDual a) ↔ IsRightRegular
 a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isRightRegular_toDual {a : α} : IsRightRegular (toDual a) ↔ IsRightRegular a := .rfl

@[to_additive (attr := simp)]
/-
**isRightRegular_ofDual** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isRightRegular_ofDual {a : αᵒᵈ} : IsRightRegular (ofDual a) ↔ IsRightRegul
ar a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isRightRegular_ofDual {a : αᵒᵈ} : IsRightRegular (ofDual a) ↔ IsRightRegular a := .rfl

@[to_additive (attr := simp)]
/-
**isRegular_toDual** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isRegular_toDual {a : α} : IsRegular (toDual a) ↔ IsRegular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isRegular_toDual {a : α} : IsRegular (toDual a) ↔ IsRegular a := .rfl

@[to_additive (attr := simp)]
/-
**isRegular_ofDual** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isRegular_ofDual {a : αᵒᵈ} : IsRegular (ofDual a) ↔ IsRegular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isRegular_ofDual {a : αᵒᵈ} : IsRegular (ofDual a) ↔ IsRegular a := .rfl

end Monoid

/-! ### Lexicographical order -/


namespace Lex

set_option backward.inferInstanceAs.wrap.instances false in
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [One α] : One (Lex α) := inferInstanceAs <| One α

set_option backward.inferInstanceAs.wrap.instances false in
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Mul α] : Mul (Lex α) := inferInstanceAs <| Mul α

set_option backward.inferInstanceAs.wrap.instances false in
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Inv α] : Inv (Lex α) := inferInstanceAs <| Inv α

set_option backward.inferInstanceAs.wrap.instances false in
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Div α] : Div (Lex α) := inferInstanceAs <| Div α

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive (attr := to_additive) (reorder := 1 2) instSMul]
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Pow α β] : Pow (Lex α) β := inferInstanceAs <| Pow α β

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive (attr := to_additive) (reorder := 1 2) instSMul']
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Pow α β] : Pow α (Lex β) := inferInstanceAs <| Pow α β

@[to_additive]
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semigroup α] : Semigroup (Lex α) := inferInstanceAs <| Semigroup α

@[to_additive]
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommSemigroup α] : CommSemigroup (Lex α) := inferInstanceAs <| CommSemigroup α

@[to_additive]
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul α] [IsLeftCancelMul α] : IsLeftCancelMul (Lex α) :=
  inferInstanceAs <| IsLeftCancelMul α

@[to_additive]
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul α] [IsRightCancelMul α] : IsRightCancelMul (Lex α) :=
  inferInstanceAs <| IsRightCancelMul α

@[to_additive]
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul α] [IsCancelMul α] : IsCancelMul (Lex α) :=
  inferInstanceAs <| IsCancelMul α

@[to_additive]
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LeftCancelSemigroup α] : LeftCancelSemigroup (Lex α) :=
  inferInstanceAs <| LeftCancelSemigroup α

@[to_additive]
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [RightCancelSemigroup α] : RightCancelSemigroup (Lex α) :=
  inferInstanceAs <| RightCancelSemigroup α

@[to_additive]
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulOneClass α] : MulOneClass (Lex α) := inferInstanceAs <| MulOneClass α

@[to_additive]
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid α] : Monoid (Lex α) := inferInstanceAs <| Monoid α

@[to_additive]
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommMonoid α] : CommMonoid (Lex α) := inferInstanceAs <| CommMonoid α

@[to_additive]
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LeftCancelMonoid α] : LeftCancelMonoid (Lex α) := inferInstanceAs <| LeftCancelMonoid α

@[to_additive]
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [RightCancelMonoid α] : RightCancelMonoid (Lex α) := inferInstanceAs <| RightCancelMonoid α

@[to_additive]
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CancelMonoid α] : CancelMonoid (Lex α) := inferInstanceAs <| CancelMonoid α

@[to_additive]
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CancelCommMonoid α] : CancelCommMonoid (Lex α) := inferInstanceAs <| CancelCommMonoid α

@[to_additive]
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [InvolutiveInv α] : InvolutiveInv (Lex α) := inferInstanceAs <| InvolutiveInv α

@[to_additive]
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DivInvMonoid α] : DivInvMonoid (Lex α) := inferInstanceAs <| DivInvMonoid α

@[to_additive]
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DivisionMonoid α] : DivisionMonoid (Lex α) := inferInstanceAs <| DivisionMonoid α

@[to_additive]
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DivisionCommMonoid α] : DivisionCommMonoid (Lex α) :=
  inferInstanceAs <| DivisionCommMonoid α

@[to_additive]
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Group α] : Group (Lex α) := inferInstanceAs <| Group α

@[to_additive]
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommGroup α] : CommGroup (Lex α) := inferInstanceAs <| CommGroup α

end Lex

@[to_additive (attr := simp)]
/-
**toLex_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toLex_one [One α] : toLex (1 : α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLex_one [One α] : toLex (1 : α) = 1 := rfl

@[to_additive (attr := simp)]
/-
**toLex_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toLex_eq_one [One α] {a : α} : toLex a = 1 ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toLex_eq_one [One α] {a : α} : toLex a = 1 ↔ a = 1 := .rfl

@[to_additive (attr := simp)]
/-
**ofLex_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofLex_one [One α] : (ofLex 1 : α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLex_one [One α] : (ofLex 1 : α) = 1 := rfl

@[to_additive (attr := simp)]
/-
**ofLex_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofLex_eq_one [One α] {a : Lex α} : ofLex a = 1 ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofLex_eq_one [One α] {a : Lex α} : ofLex a = 1 ↔ a = 1 := .rfl

@[to_additive (attr := simp)]
/-
**toLex_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toLex_mul [Mul α] (a b : α) : toLex (a * b) = toLex a * toLex b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLex_mul [Mul α] (a b : α) : toLex (a * b) = toLex a * toLex b := rfl

@[to_additive (attr := simp)]
/-
**ofLex_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofLex_mul [Mul α] (a b : Lex α) : ofLex (a * b) = ofLex a * ofLex b
参数：a b : Lex α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLex_mul [Mul α] (a b : Lex α) : ofLex (a * b) = ofLex a * ofLex b := rfl

@[to_additive (attr := simp)]
/-
**toLex_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toLex_inv [Inv α] (a : α) : toLex a⁻¹ = (toLex a)⁻¹
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLex_inv [Inv α] (a : α) : toLex a⁻¹ = (toLex a)⁻¹ := rfl

@[to_additive (attr := simp)]
/-
**ofLex_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofLex_inv [Inv α] (a : Lex α) : ofLex a⁻¹ = (ofLex a)⁻¹
参数：a : Lex α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLex_inv [Inv α] (a : Lex α) : ofLex a⁻¹ = (ofLex a)⁻¹ := rfl

@[to_additive (attr := simp)]
/-
**toLex_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toLex_div [Div α] (a b : α) : toLex (a / b) = toLex a / toLex b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLex_div [Div α] (a b : α) : toLex (a / b) = toLex a / toLex b := rfl

@[to_additive (attr := simp)]
/-
**ofLex_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofLex_div [Div α] (a b : Lex α) : ofLex (a / b) = ofLex a / ofLex b
参数：a b : Lex α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLex_div [Div α] (a b : Lex α) : ofLex (a / b) = ofLex a / ofLex b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toLex_smul]
/-
**toLex_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toLex_pow [Pow α β] (a : α) (b : β) : toLex (a ^ b) = toLex a ^ b
参数：a : α；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLex_pow [Pow α β] (a : α) (b : β) : toLex (a ^ b) = toLex a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofLex_smul]
/-
**ofLex_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofLex_pow [Pow α β] (a : Lex α) (b : β) : ofLex (a ^ b) = ofLex a ^ b
参数：a : Lex α；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLex_pow [Pow α β] (a : Lex α) (b : β) : ofLex (a ^ b) = ofLex a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toLex_smul']
/-
**pow_toLex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_toLex [Pow α β] (a : α) (b : β) : a ^ toLex b = a ^ b
参数：a : α；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_toLex [Pow α β] (a : α) (b : β) : a ^ toLex b = a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofLex_smul']
/-
**pow_ofLex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_ofLex [Pow α β] (a : α) (b : Lex β) : a ^ ofLex b = a ^ b
参数：a : α；b : Lex β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_ofLex [Pow α β] (a : α) (b : Lex β) : a ^ ofLex b = a ^ b := rfl

section Monoid
variable [Monoid α]

@[to_additive (attr := simp)]
/-
**isLeftRegular_toLex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLeftRegular_toLex {a : α} : IsLeftRegular (toLex a) ↔ IsLeftRegular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLeftRegular_toLex {a : α} : IsLeftRegular (toLex a) ↔ IsLeftRegular a := .rfl

@[to_additive (attr := simp)]
/-
**isLeftRegular_ofLex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLeftRegular_ofLex {a : Lex α} : IsLeftRegular (ofLex a) ↔ IsLeftRegular 
a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLeftRegular_ofLex {a : Lex α} : IsLeftRegular (ofLex a) ↔ IsLeftRegular a := .rfl

@[to_additive (attr := simp)]
/-
**isRightRegular_toLex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isRightRegular_toLex {a : α} : IsRightRegular (toLex a) ↔ IsRightRegular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isRightRegular_toLex {a : α} : IsRightRegular (toLex a) ↔ IsRightRegular a := .rfl

@[to_additive (attr := simp)]
/-
**isRightRegular_ofLex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isRightRegular_ofLex {a : Lex α} : IsRightRegular (ofLex a) ↔ IsRightRegul
ar a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isRightRegular_ofLex {a : Lex α} : IsRightRegular (ofLex a) ↔ IsRightRegular a := .rfl

@[to_additive (attr := simp)]
/-
**isRegular_toLex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isRegular_toLex {a : α} : IsRegular (toLex a) ↔ IsRegular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isRegular_toLex {a : α} : IsRegular (toLex a) ↔ IsRegular a := .rfl

@[to_additive (attr := simp)]
/-
**isRegular_ofLex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isRegular_ofLex {a : Lex α} : IsRegular (ofLex a) ↔ IsRegular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isRegular_ofLex {a : Lex α} : IsRegular (ofLex a) ↔ IsRegular a := .rfl

end Monoid

/-! ### Colexicographical order -/


namespace Colex

set_option backward.inferInstanceAs.wrap.instances false in
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [One α] : One (Colex α) := inferInstanceAs <| One α

set_option backward.inferInstanceAs.wrap.instances false in
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Mul α] : Mul (Colex α) := inferInstanceAs <| Mul α

set_option backward.inferInstanceAs.wrap.instances false in
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Inv α] : Inv (Colex α) := inferInstanceAs <| Inv α

set_option backward.inferInstanceAs.wrap.instances false in
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Div α] : Div (Colex α) := inferInstanceAs <| Div α

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive (attr := to_additive) (reorder := 1 2) instSMul]
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Pow α β] : Pow (Colex α) β := inferInstanceAs <| Pow α β

set_option backward.inferInstanceAs.wrap.instances false in
@[to_additive (attr := to_additive) (reorder := 1 2) instSMul']
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Pow α β] : Pow α (Colex β) := inferInstanceAs <| Pow α β

@[to_additive]
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semigroup α] : Semigroup (Colex α) := inferInstanceAs <| Semigroup α

@[to_additive]
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommSemigroup α] : CommSemigroup (Colex α) := inferInstanceAs <| CommSemigroup α

@[to_additive]
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul α] [IsLeftCancelMul α] : IsLeftCancelMul (Colex α) :=
  inferInstanceAs <| IsLeftCancelMul α

@[to_additive]
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul α] [IsRightCancelMul α] : IsRightCancelMul (Colex α) :=
  inferInstanceAs <| IsRightCancelMul α

@[to_additive]
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul α] [IsCancelMul α] : IsCancelMul (Colex α) :=
  inferInstanceAs <| IsCancelMul α

@[to_additive]
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LeftCancelSemigroup α] : LeftCancelSemigroup (Colex α) :=
  inferInstanceAs <| LeftCancelSemigroup α

@[to_additive]
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [RightCancelSemigroup α] : RightCancelSemigroup (Colex α) :=
  inferInstanceAs <| RightCancelSemigroup α

@[to_additive]
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulOneClass α] : MulOneClass (Colex α) := inferInstanceAs <| MulOneClass α

@[to_additive]
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid α] : Monoid (Colex α) := inferInstanceAs <| Monoid α

@[to_additive]
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommMonoid α] : CommMonoid (Colex α) := inferInstanceAs <| CommMonoid α

@[to_additive]
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LeftCancelMonoid α] : LeftCancelMonoid (Colex α) := inferInstanceAs <| LeftCancelMonoid α

@[to_additive]
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [RightCancelMonoid α] : RightCancelMonoid (Colex α) :=
  inferInstanceAs <| RightCancelMonoid α

@[to_additive]
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CancelMonoid α] : CancelMonoid (Colex α) := inferInstanceAs <| CancelMonoid α

@[to_additive]
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CancelCommMonoid α] : CancelCommMonoid (Colex α) := inferInstanceAs <| CancelCommMonoid α

@[to_additive]
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [InvolutiveInv α] : InvolutiveInv (Colex α) := inferInstanceAs <| InvolutiveInv α

@[to_additive]
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DivInvMonoid α] : DivInvMonoid (Colex α) := inferInstanceAs <| DivInvMonoid α

@[to_additive]
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DivisionMonoid α] : DivisionMonoid (Colex α) := inferInstanceAs <| DivisionMonoid α

@[to_additive]
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DivisionCommMonoid α] : DivisionCommMonoid (Colex α) :=
  inferInstanceAs <| DivisionCommMonoid α

@[to_additive]
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Group α] : Group (Colex α) := inferInstanceAs <| Group α

@[to_additive]
/-
**Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommGroup α] : CommGroup (Colex α) := inferInstanceAs <| CommGroup α

end Colex

@[to_additive (attr := simp)]
/-
**toColex_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toColex_one [One α] : toColex (1 : α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toColex_one [One α] : toColex (1 : α) = 1 := rfl

@[to_additive (attr := simp)]
/-
**toColex_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toColex_eq_one [One α] {a : α} : toColex a = 1 ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toColex_eq_one [One α] {a : α} : toColex a = 1 ↔ a = 1 := .rfl

@[to_additive (attr := simp)]
/-
**ofColex_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofColex_one [One α] : (ofColex 1 : α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofColex_one [One α] : (ofColex 1 : α) = 1 := rfl

@[to_additive (attr := simp)]
/-
**ofColex_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofColex_eq_one [One α] {a : Colex α} : ofColex a = 1 ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofColex_eq_one [One α] {a : Colex α} : ofColex a = 1 ↔ a = 1 := .rfl

@[to_additive (attr := simp)]
/-
**toColex_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toColex_mul [Mul α] (a b : α) : toColex (a * b) = toColex a * toColex b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toColex_mul [Mul α] (a b : α) : toColex (a * b) = toColex a * toColex b := rfl

@[to_additive (attr := simp)]
/-
**ofColex_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofColex_mul [Mul α] (a b : Colex α) : ofColex (a * b) = ofColex a * ofCole
x b
参数：a b : Colex α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofColex_mul [Mul α] (a b : Colex α) : ofColex (a * b) = ofColex a * ofColex b := rfl

@[to_additive (attr := simp)]
/-
**toColex_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toColex_inv [Inv α] (a : α) : toColex a⁻¹ = (toColex a)⁻¹
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toColex_inv [Inv α] (a : α) : toColex a⁻¹ = (toColex a)⁻¹ := rfl

@[to_additive (attr := simp)]
/-
**ofColex_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofColex_inv [Inv α] (a : Colex α) : ofColex a⁻¹ = (ofColex a)⁻¹
参数：a : Colex α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofColex_inv [Inv α] (a : Colex α) : ofColex a⁻¹ = (ofColex a)⁻¹ := rfl

@[to_additive (attr := simp)]
/-
**toColex_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toColex_div [Div α] (a b : α) : toColex (a / b) = toColex a / toColex b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toColex_div [Div α] (a b : α) : toColex (a / b) = toColex a / toColex b := rfl

@[to_additive (attr := simp)]
/-
**ofColex_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofColex_div [Div α] (a b : Colex α) : ofColex (a / b) = ofColex a / ofCole
x b
参数：a b : Colex α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofColex_div [Div α] (a b : Colex α) : ofColex (a / b) = ofColex a / ofColex b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toColex_smul]
/-
**toColex_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toColex_pow [Pow α β] (a : α) (b : β) : toColex (a ^ b) = toColex a ^ b
参数：a : α；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toColex_pow [Pow α β] (a : α) (b : β) : toColex (a ^ b) = toColex a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofColex_smul]
/-
**ofColex_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofColex_pow [Pow α β] (a : Colex α) (b : β) : ofColex (a ^ b) = ofColex a 
^ b
参数：a : Colex α；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofColex_pow [Pow α β] (a : Colex α) (b : β) : ofColex (a ^ b) = ofColex a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toColex_smul']
/-
**pow_toColex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_toColex [Pow α β] (a : α) (b : β) : a ^ toColex b = a ^ b
参数：a : α；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_toColex [Pow α β] (a : α) (b : β) : a ^ toColex b = a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofColex_smul']
/-
**pow_ofColex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_ofColex [Pow α β] (a : α) (b : Colex β) : a ^ ofColex b = a ^ b
参数：a : α；b : Colex β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_ofColex [Pow α β] (a : α) (b : Colex β) : a ^ ofColex b = a ^ b := rfl

section Monoid
variable [Monoid α]

@[to_additive (attr := simp)]
/-
**isLeftRegular_toColex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLeftRegular_toColex {a : α} : IsLeftRegular (toColex a) ↔ IsLeftRegular 
a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLeftRegular_toColex {a : α} : IsLeftRegular (toColex a) ↔ IsLeftRegular a := .rfl

@[to_additive (attr := simp)]
/-
**isLeftRegular_ofColex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLeftRegular_ofColex {a : Colex α} : IsLeftRegular (ofColex a) ↔ IsLeftRe
gular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLeftRegular_ofColex {a : Colex α} : IsLeftRegular (ofColex a) ↔ IsLeftRegular a := .rfl

@[to_additive (attr := simp)]
/-
**isRightRegular_toColex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isRightRegular_toColex {a : α} : IsRightRegular (toColex a) ↔ IsRightRegul
ar a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isRightRegular_toColex {a : α} : IsRightRegular (toColex a) ↔ IsRightRegular a := .rfl

@[to_additive (attr := simp)]
/-
**isRightRegular_ofColex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isRightRegular_ofColex {a : Colex α} : IsRightRegular (ofColex a) ↔ IsRigh
tRegular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isRightRegular_ofColex {a : Colex α} : IsRightRegular (ofColex a) ↔ IsRightRegular a := .rfl

@[to_additive (attr := simp)]
/-
**isRegular_toColex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isRegular_toColex {a : α} : IsRegular (toColex a) ↔ IsRegular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isRegular_toColex {a : α} : IsRegular (toColex a) ↔ IsRegular a := .rfl

@[to_additive (attr := simp)]
/-
**isRegular_ofColex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isRegular_ofColex {a : Colex α} : IsRegular (ofColex a) ↔ IsRegular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isRegular_ofColex {a : Colex α} : IsRegular (ofColex a) ↔ IsRegular a := .rfl

end Monoid

