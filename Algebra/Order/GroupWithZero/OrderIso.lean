/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Equiv
public import Mathlib.Order.Hom.Basic

/-!
# Multiplication by a positive element as an order isomorphism
-/

@[expose] public section

variable {G₀ : Type*} [GroupWithZero G₀]

namespace OrderIso

variable [PartialOrder G₀]

section left
variable [PosMulReflectLT G₀]

attribute [local instance] PosMulReflectLT.toPosMulStrictMono PosMulReflectLT.toPosMulReflectLE

/-- `Equiv.mulLeft₀` as an order isomorphism. -/
@[simps! +simpRhs]
/-
**OrderIso.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderIso.mulLeft (a : α) : α ≃o α where map_rel_iff' {_ _}
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.mulLeft₀` as an order isomorphism.
-/
def mulLeft₀ (a : G₀) (ha : 0 < a) : G₀ ≃o G₀ where
  toEquiv := .mulLeft₀ a ha.ne'
  map_rel_iff' := mul_le_mul_iff_right₀ ha
/-
**OrderIso.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderIso.mulLeft (a : α) : α ≃o α where map_rel_iff' {_ _}
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mulLeft₀_symm (a : G₀) (ha : 0 < a) : (mulLeft₀ a ha).symm = mulLeft₀ a⁻¹ (inv_pos.2 ha) := by
  ext; rfl

end left

attribute [local instance] MulPosReflectLT.toMulPosStrictMono MulPosReflectLT.toMulPosReflectLE

section right
variable [MulPosReflectLT G₀]

/-- `Equiv.mulRight₀` as an order isomorphism. -/
@[simps! +simpRhs]
/-
**OrderIso.mulRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderIso.mulRight (a : α) : α ≃o α where map_rel_iff' {_ _}
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.mulRight₀` as an order isomorphism.
-/
def mulRight₀ (a : G₀) (ha : 0 < a) : G₀ ≃o G₀ where
  toEquiv := .mulRight₀ a ha.ne'
  map_rel_iff' := mul_le_mul_iff_left₀ ha
/-
**OrderIso.mulRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderIso.mulRight (a : α) : α ≃o α where map_rel_iff' {_ _}
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mulRight₀_symm (a : G₀) (ha : 0 < a) :
    (mulRight₀ a ha).symm = mulRight₀ a⁻¹ (Right.inv_pos.2 ha) := by ext; rfl

/-- `Equiv.divRight₀` as an order isomorphism. -/
@[simps! +simpRhs]
/-
**OrderIso.divRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderIso.divRight (a : α) : α ≃o α where toEquiv
参数：a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `div_le_div_iff_right`：div_le_div_iff_right (c : α) : a / c <= b / c ↔ a 
<= b

--- 原说明 ---
`Equiv.divRight₀` as an order isomorphism.
-/
def divRight₀ (a : G₀) (ha : 0 < a) : G₀ ≃o G₀ where
  toEquiv := .divRight₀ a ha.ne'
  map_rel_iff' {b c} := by
    simp only [Equiv.divRight₀_apply, div_eq_mul_inv]
    exact mul_le_mul_iff_left₀ (a := a⁻¹) (Right.inv_pos.mpr ha)

end right

end OrderIso
section Lattice

/-
**mul_inf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_inf [MulLeftMono α] (a b c : α) : c * (a ⊓ b) = c * a ⊓ c * b
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_inf`：OrderIso.map_inf [SemilatticeInf α] [SemilatticeInf β]
 (f : α ≃o β) (x y : α) : f (x ⊓ y) = f x ⊓ f y
-/
lemma mul_inf₀ [SemilatticeInf G₀] [PosMulReflectLT G₀] {c : G₀} (hc : 0 ≤ c) (a b : G₀) :
    c * (a ⊓ b) = c * a ⊓ c * b := by
  obtain (rfl | hc) := hc.eq_or_lt
  · simp
  · exact (OrderIso.mulLeft₀ c hc).map_inf a b
/-
**mul_sup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_sup [MulLeftMono α] (a b c : α) : c * (a ⊔ b) = c * a ⊔ c * b
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] [inst_1 : SemilatticeSup β] (f : α ≃o β) (x y : α),   f (x ⊔ y) = f x ⊔ f y
-/
lemma mul_sup₀ [SemilatticeSup G₀] [PosMulReflectLT G₀] {c : G₀} (hc : 0 ≤ c) (a b : G₀) :
    c * (a ⊔ b) = c * a ⊔ c * b := by
  obtain (rfl | hc) := hc.eq_or_lt
  · simp
  · exact (OrderIso.mulLeft₀ c hc).map_sup a b
/-
**inf_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inf_mul [MulRightMono α] (a b c : α) : (a ⊓ b) * c = a * c ⊓ b * c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_inf`：OrderIso.map_inf [SemilatticeInf α] [SemilatticeInf β]
 (f : α ≃o β) (x y : α) : f (x ⊓ y) = f x ⊓ f y
-/
lemma inf_mul₀ [SemilatticeInf G₀] [MulPosReflectLT G₀] {c : G₀} (hc : 0 ≤ c) (a b : G₀) :
    (a ⊓ b) * c = a * c ⊓ b * c := by
  obtain (rfl | hc) := hc.eq_or_lt
  · simp
  · exact (OrderIso.mulRight₀ c hc).map_inf a b
/-
**sup_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sup_mul [MulRightMono α] (a b c : α) : (a ⊔ b) * c = a * c ⊔ b * c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] [inst_1 : SemilatticeSup β] (f : α ≃o β) (x y : α),   f (x ⊔ y) = f x ⊔ f y
-/
lemma sup_mul₀ [SemilatticeSup G₀] [MulPosReflectLT G₀] {c : G₀} (hc : 0 ≤ c) (a b : G₀) :
    (a ⊔ b) * c = a * c ⊔ b * c := by
  obtain (rfl | hc) := hc.eq_or_lt
  · simp
  · exact (OrderIso.mulRight₀ c hc).map_sup a b

end Lattice

