/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Order.Hom.Monoid

/-!
# Isomorphism of submonoids of ordered monoids
-/

@[expose] public section

/-- The top submonoid is order isomorphic to the whole monoid. -/
@[simps!]
/-
**Submonoid.topOrderMonoidIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submonoid.topOrderMonoidIso {α : Type*} [Preorder α] [Monoid α] : (⊤ : Sub
monoid α) ≃*o α where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The top submonoid is order isomorphic to the whole monoid.
-/
def Submonoid.topOrderMonoidIso {α : Type*} [Preorder α] [Monoid α] : (⊤ : Submonoid α) ≃*o α where
  __ := Submonoid.topEquiv
  map_le_map_iff' := Iff.rfl
