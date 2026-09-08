/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.Monoid.Basic

/-!
# Ordered instances on submodules
-/

public section

namespace Submodule
variable {R M : Type*}

section OrderedMonoid
variable [Semiring R]

/-- A submodule of an ordered additive monoid is an ordered additive monoid. -/
/-
**Submodule.toIsOrderedAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：toIsOrderedAddMonoid [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoi
d M] [Module R M] (S : Submodule R M) : IsOrderedAddMonoid S
参数：S : Submodule R M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isOrderedAddMonoid`：∀ {α : Type u} {β : Type u_1} [in
st : AddCommMonoid α] [inst_1 : Preorder α] [IsOrderedAddMonoid α]   [inst_3 : A
ddCommMonoid β] [inst_4 : P…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A submodule of an ordered additive monoid is an ordered additive monoid.
-/
instance toIsOrderedAddMonoid [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
    [Module R M] (S : Submodule R M) :
    IsOrderedAddMonoid S :=
  Function.Injective.isOrderedAddMonoid Subtype.val (fun _ _ => rfl) .rfl

/-- A submodule of an ordered cancellative additive monoid is an ordered cancellative additive
monoid. -/
/-
**Submodule.toIsOrderedCancelAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：toIsOrderedCancelAddMonoid [AddCommMonoid M] [PartialOrder M] [IsOrderedCa
ncelAddMonoid M] [Module R M] (S : Submodule R M) : IsOrderedCancelAddMonoid S
参数：S : Submodule R M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isOrderedCancelAddMonoid`：∀ {α : Type u} {β : Type u_
1} [inst : AddCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α]  
 [inst_3 : AddCommMonoid β] [inst…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A submodule of an ordered cancellative additive monoid is an ordered cancellativ
e additive
monoid.
-/
instance toIsOrderedCancelAddMonoid [AddCommMonoid M] [PartialOrder M]
    [IsOrderedCancelAddMonoid M] [Module R M] (S : Submodule R M) :
    IsOrderedCancelAddMonoid S :=
  Function.Injective.isOrderedCancelAddMonoid Subtype.val (fun _ _ => rfl) .rfl

end OrderedMonoid

end Submodule

