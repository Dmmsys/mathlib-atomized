/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Order.AddGroupWithTop
/-!
# Instances on PUnit

This file collects facts about ordered algebraic structures on the one-element type.
-/

public section

namespace PUnit

/-
**PUnit.canonicallyOrderedAdd** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
形式化陈述：canonicallyOrderedAdd : CanonicallyOrderedAdd PUnit where exists_add_of_le
 {_ _} _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `trivial`：True
-/
instance canonicallyOrderedAdd : CanonicallyOrderedAdd PUnit where
  exists_add_of_le {_ _} _ := ⟨unit, by subsingleton⟩
  le_add_self _ _ := trivial
  le_self_add _ _ := trivial
/-
**PUnit.isOrderedCancelAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
形式化陈述：isOrderedCancelAddMonoid : IsOrderedCancelAddMonoid PUnit where le_of_add_
le_add_left _ _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `trivial`：True
-/
instance isOrderedCancelAddMonoid : IsOrderedCancelAddMonoid PUnit where
  le_of_add_le_add_left _ _ _ _ := trivial
  add_le_add_left := by intros; rfl
/-
**PUnit.** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearOrderedAddCommMonoidWithTop PUnit where
  top := ()
  le_top _ := le_rfl
  top_add' _ := rfl
  isAddLeftRegular_of_ne_top := by simp

end PUnit

