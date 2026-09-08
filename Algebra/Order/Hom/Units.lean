/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Algebra.Order.Monoid.Units

/-! # Isomorphism of ordered monoids descends to units
-/

@[expose] public section

variable {α β : Type*} [Preorder α] [Monoid α] [Preorder β] [Monoid β] (e : α ≃*o β)

/-- An isomorphism of ordered monoids descends to their units. -/
@[simps!]
/-
**OrderMonoidIso.unitsCongr** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderMonoidIso.unitsCongr : αˣ ≃*o βˣ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of ordered monoids descends to their units.
-/
def OrderMonoidIso.unitsCongr : αˣ ≃*o βˣ where
  __ := Units.mapEquiv e.toMulEquiv
  map_le_map_iff' {x y} := by simp [← Units.val_le_val]
/-
**OrderMonoidIso.unitsCongr_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：OrderMonoidIso.unitsCongr_symm_apply (x : βˣ) : e.unitsCongr.symm x = e.sy
mm x
参数：x : βˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma OrderMonoidIso.unitsCongr_symm_apply (x : βˣ) : e.unitsCongr.symm x = e.symm x := rfl
