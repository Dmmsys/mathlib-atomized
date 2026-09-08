/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Order.Hom.Basic

/-!
# Inverse and multiplication as order isomorphisms in ordered groups

-/

@[expose] public section

open Function

universe u

variable {α : Type u}

section Group

variable [Group α]

section TypeclassesLeftRightLE

variable [LE α] [MulLeftMono α] [MulRightMono α] {a b : α}

section

variable (α)

/-- `x ↦ x⁻¹` as an order-reversing equivalence. -/
@[to_additive (attr := simps!) /-- `x ↦ -x` as an order-reversing equivalence. -/]
/-
**OrderIso.inv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderIso.inv : α ≃o αᵒᵈ where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `inv_le_inv_iff`：inv_le_inv_iff : a⁻¹ <= b⁻¹ ↔ b <= a

--- 原说明 ---
`x ↦ x⁻¹` as an order-reversing equivalence.
-/
def OrderIso.inv : α ≃o αᵒᵈ where
  toEquiv := (Equiv.inv α).trans OrderDual.toDual
  map_rel_iff' {_ _} := inv_le_inv_iff (α := α)

end

@[to_additive neg_le]
/-
**inv_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_le' : a⁻¹ <= b ↔ b⁻¹ <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.symm_apply_le`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [i
nst_1 : LE β] (e : α ≃o β) {x : α} {y : β}, e.symm y ≤ x ↔ y ≤ e x
-/
theorem inv_le' : a⁻¹ ≤ b ↔ b⁻¹ ≤ a :=
  (OrderIso.inv α).symm_apply_le

alias ⟨inv_le_of_inv_le', _⟩ := inv_le'

attribute [to_additive neg_le_of_neg_le] inv_le_of_inv_le'

@[to_additive le_neg]
/-
**le_inv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_inv' : a <= b⁻¹ ↔ b <= a⁻¹
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.le_symm_apply`：le_symm_apply (e : α ≃o β) {x : α} {y : β} : x <
= e.symm y ↔ e x <= y
-/
theorem le_inv' : a ≤ b⁻¹ ↔ b ≤ a⁻¹ :=
  (OrderIso.inv α).le_symm_apply

/-- `x ↦ a / x` as an order-reversing equivalence. -/
@[to_additive (attr := simps!) /-- `x ↦ a - x` as an order-reversing equivalence. -/]
/-
**OrderIso.divLeft** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderIso.divLeft (a : α) : α ≃o αᵒᵈ where toEquiv
参数：a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `div_le_div_iff_left`：div_le_div_iff_left (a : α) : a / b <= a / c ↔ c <=
 b

--- 原说明 ---
`x ↦ a / x` as an order-reversing equivalence.
-/
def OrderIso.divLeft (a : α) : α ≃o αᵒᵈ where
  toEquiv := (Equiv.divLeft a).trans OrderDual.toDual
  map_rel_iff' {_ _} := div_le_div_iff_left (α := α) _

end TypeclassesLeftRightLE

end Group

alias ⟨le_inv_of_le_inv, _⟩ := le_inv'

attribute [to_additive] le_inv_of_le_inv

section Group

variable [Group α] [LE α]

section Right

variable [MulRightMono α] {a : α}

/-- `Equiv.mulRight` as an `OrderIso`. See also `OrderEmbedding.mulRight`. -/
@[to_additive (attr := simps! +simpRhs toEquiv apply)
  /-- `Equiv.addRight` as an `OrderIso`. See also `OrderEmbedding.addRight`. -/]
/-
**OrderIso.mulRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderIso.mulRight (a : α) : α ≃o α where map_rel_iff' {_ _}
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def OrderIso.mulRight (a : α) : α ≃o α where
  map_rel_iff' {_ _} := mul_le_mul_iff_right a
  toEquiv := Equiv.mulRight a

@[to_additive (attr := simp)]
/-
**OrderIso.mulRight_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.mulRight_symm (a : α) : (OrderIso.mulRight a).symm = OrderIso.mul
Right a⁻¹
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.ext`：ext {f g : α ≃o β} (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem OrderIso.mulRight_symm (a : α) : (OrderIso.mulRight a).symm = OrderIso.mulRight a⁻¹ := by
  ext x
  rfl

/-- `x ↦ x / a` as an order isomorphism. -/
@[to_additive (attr := simps!) /-- `x ↦ x - a` as an order isomorphism. -/]
/-
**OrderIso.divRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderIso.divRight (a : α) : α ≃o α where toEquiv
参数：a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `div_le_div_iff_right`：div_le_div_iff_right (c : α) : a / c <= b / c ↔ a 
<= b

--- 原说明 ---
`x ↦ x / a` as an order isomorphism.
-/
def OrderIso.divRight (a : α) : α ≃o α where
  toEquiv := Equiv.divRight a
  map_rel_iff' {_ _} := div_le_div_iff_right a

end Right

section Left

variable [MulLeftMono α]

/-- `Equiv.mulLeft` as an `OrderIso`. See also `OrderEmbedding.mulLeft`. -/
@[to_additive (attr := simps! +simpRhs toEquiv apply)
  /-- `Equiv.addLeft` as an `OrderIso`. See also `OrderEmbedding.addLeft`. -/]
/-
**OrderIso.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderIso.mulLeft (a : α) : α ≃o α where map_rel_iff' {_ _}
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def OrderIso.mulLeft (a : α) : α ≃o α where
  map_rel_iff' {_ _} := mul_le_mul_iff_left a
  toEquiv := Equiv.mulLeft a

@[to_additive (attr := simp)]
/-
**OrderIso.mulLeft_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.mulLeft_symm (a : α) : (OrderIso.mulLeft a).symm = OrderIso.mulLe
ft a⁻¹
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.ext`：ext {f g : α ≃o β} (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem OrderIso.mulLeft_symm (a : α) : (OrderIso.mulLeft a).symm = OrderIso.mulLeft a⁻¹ := by
  ext x
  rfl

end Left

end Group

