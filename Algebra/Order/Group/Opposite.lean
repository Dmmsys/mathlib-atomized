/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Order.Monoid.Defs

/-!
# Order instances for `MulOpposite`/`AddOpposite`

This file transfers order instances and ordered monoid/group instances from `α` to `αᵐᵒᵖ` and
`αᵃᵒᵖ`.
-/

public section

variable {α : Type*}

namespace MulOpposite
section Preorder
variable [Preorder α]

/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance : Preorder αᵐᵒᵖ := Preorder.lift unop
/-
**MulOpposite.unop_le_unop** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : αᵐᵒᵖ}, MulOpposite.unop a ≤ Mu
lOpposite.unop b ↔ a ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive (attr := simp)] lemma unop_le_unop {a b : αᵐᵒᵖ} : a.unop ≤ b.unop ↔ a ≤ b := .rfl
/-
**MulOpposite.op_le_op** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, MulOpposite.op a ≤ MulOppo
site.op b ↔ a ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive (attr := simp)] lemma op_le_op {a b : α} : op a ≤ op b ↔ a ≤ b := .rfl

end Preorder

/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [PartialOrder α] : PartialOrder αᵐᵒᵖ := PartialOrder.lift _ unop_injective

section OrderedCommMonoid
variable [CommMonoid α] [PartialOrder α]

/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [IsOrderedMonoid α] : IsOrderedMonoid αᵐᵒᵖ where
  mul_le_mul_left a b hab c := mul_le_mul_right (by simpa) c.unop
/-
**MulOpposite.unop_le_one** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : CommMonoid α] [inst_1 : PartialOrder α] {a : αᵐᵒᵖ
}, MulOpposite.unop a ≤ 1 ↔ a ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive (attr := simp)] lemma unop_le_one {a : αᵐᵒᵖ} : unop a ≤ 1 ↔ a ≤ 1 := .rfl
/-
**MulOpposite.one_le_unop** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : CommMonoid α] [inst_1 : PartialOrder α] {a : αᵐᵒᵖ
}, 1 ≤ MulOpposite.unop a ↔ 1 ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive (attr := simp)] lemma one_le_unop {a : αᵐᵒᵖ} : 1 ≤ unop a ↔ 1 ≤ a := .rfl
/-
**MulOpposite.op_le_one** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : CommMonoid α] [inst_1 : PartialOrder α] {a : α}, 
MulOpposite.op a ≤ 1 ↔ a ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive (attr := simp)] lemma op_le_one {a : α} : op a ≤ 1 ↔ a ≤ 1 := .rfl
/-
**MulOpposite.one_le_op** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : CommMonoid α] [inst_1 : PartialOrder α] {a : α}, 
1 ≤ MulOpposite.op a ↔ 1 ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive (attr := simp)] lemma one_le_op {a : α} : 1 ≤ op a ↔ 1 ≤ a := .rfl

end OrderedCommMonoid

section OrderedAddCommMonoid
variable [AddCommMonoid α] [PartialOrder α]

/-
**MulOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsOrderedAddMonoid α] : IsOrderedAddMonoid αᵐᵒᵖ where
  add_le_add_left a b hab c := add_le_add_left (by simpa) c.unop
/-
**MulOpposite.unop_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] {a : α
ᵐᵒᵖ}, MulOpposite.unop a ≤ 0 ↔ a ≤ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma unop_nonpos {a : αᵐᵒᵖ} : unop a ≤ 0 ↔ a ≤ 0 := .rfl
/-
**MulOpposite.unop_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] {a : α
ᵐᵒᵖ}, 0 ≤ MulOpposite.unop a ↔ 0 ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma unop_nonneg {a : αᵐᵒᵖ} : 0 ≤ unop a ↔ 0 ≤ a := .rfl
/-
**MulOpposite.op_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] {a : α
}, MulOpposite.op a ≤ 0 ↔ a ≤ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma op_nonpos {a : α} : op a ≤ 0 ↔ a ≤ 0 := .rfl
/-
**MulOpposite.op_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] {a : α
}, 0 ≤ MulOpposite.op a ↔ 0 ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma op_nonneg {a : α} : 0 ≤ op a ↔ 0 ≤ a := .rfl

end OrderedAddCommMonoid

end MulOpposite

namespace AddOpposite
section OrderedCommMonoid
variable [CommMonoid α] [PartialOrder α]

/-
**AddOpposite.** 是 Mathlib 中的一个实例，位于命名空间 `AddOpposite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsOrderedMonoid α] : IsOrderedMonoid αᵃᵒᵖ where
  mul_le_mul_left a b hab c := mul_le_mul_left (by simpa) c.unop
/-
**AddOpposite.unop_le_one** 是 Mathlib 中的一个定理，位于命名空间 `AddOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : CommMonoid α] [inst_1 : PartialOrder α] {a : αᵃᵒᵖ
}, AddOpposite.unop a ≤ 1 ↔ a ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma unop_le_one {a : αᵃᵒᵖ} : unop a ≤ 1 ↔ a ≤ 1 := .rfl
/-
**AddOpposite.one_le_unop** 是 Mathlib 中的一个定理，位于命名空间 `AddOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : CommMonoid α] [inst_1 : PartialOrder α] {a : αᵃᵒᵖ
}, 1 ≤ AddOpposite.unop a ↔ 1 ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma one_le_unop {a : αᵃᵒᵖ} : 1 ≤ unop a ↔ 1 ≤ a := .rfl
/-
**AddOpposite.op_le_one** 是 Mathlib 中的一个定理，位于命名空间 `AddOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : CommMonoid α] [inst_1 : PartialOrder α] {a : α}, 
AddOpposite.op a ≤ 1 ↔ a ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma op_le_one {a : α} : op a ≤ 1 ↔ a ≤ 1 := .rfl
/-
**AddOpposite.one_le_op** 是 Mathlib 中的一个定理，位于命名空间 `AddOpposite`。
形式化陈述：∀ {α : Type u_1} [inst : CommMonoid α] [inst_1 : PartialOrder α] {a : α}, 
1 ≤ AddOpposite.op a ↔ 1 ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma one_le_op {a : α} : 1 ≤ op a ↔ 1 ≤ a := .rfl

end OrderedCommMonoid

end AddOpposite

