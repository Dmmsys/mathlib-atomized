/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Order.Group.Action.End
public import Mathlib.Order.Preorder.Chain

/-!
# Action on flags

Order isomorphisms act on flags.
-/

public section

open scoped Pointwise

variable {α : Type*}

namespace Flag
variable [Preorder α]

/-
**Flag.** 是 Mathlib 中的一个实例，位于命名空间 `Flag`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul (α ≃o α) (Flag α) where smul e := map e

@[simp, norm_cast]
/-
**Flag.coe_smul** 是 Mathlib 中的一个引理，位于命名空间 `Flag`。
形式化陈述：coe_smul (e : α ≃o α) (s : Flag α) : (↑(e • s) : Set α) = e • s
参数：e : α ≃o α；s : Flag α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_smul (e : α ≃o α) (s : Flag α) : (↑(e • s) : Set α) = e • s := rfl
/-
**Flag.** 是 Mathlib 中的一个实例，位于命名空间 `Flag`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction (α ≃o α) (Flag α) := SetLike.coe_injective.mulAction _ coe_smul

end Flag

