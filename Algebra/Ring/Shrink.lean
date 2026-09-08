/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Algebra.Ring.TransferInstance

/-!
# Transfer ring structures from `α` to `Shrink α`
-/

@[expose] public section

noncomputable section

namespace Shrink
universe v
variable {α : Type*} [Small.{v} α]

variable (α) in
/-- Shrink `α` to a smaller universe preserves ring structure. -/
/-
**Shrink.ringEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Shrink`。
形式化陈述：ringEquiv [Add α] [Mul α] : Shrink.{v} α ≃+* α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Shrink `α` to a smaller universe preserves ring structure.
-/
def ringEquiv [Add α] [Mul α] : Shrink.{v} α ≃+* α := (equivShrink α).symm.ringEquiv
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalNonAssocSemiring
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalSemiring α] : NonUnitalSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalSemiring
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoidWithOne α] : AddMonoidWithOne (Shrink.{v} α) :=
  (equivShrink α).symm.addMonoidWithOne
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddGroupWithOne α] : AddGroupWithOne (Shrink.{v} α) :=
  (equivShrink α).symm.addGroupWithOne
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonAssocSemiring α] : NonAssocSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.nonAssocSemiring
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring α] : Semiring (Shrink.{v} α) := (equivShrink α).symm.semiring
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalCommSemiring α] : NonUnitalCommSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalCommSemiring
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommSemiring α] : CommSemiring (Shrink.{v} α) := (equivShrink α).symm.commSemiring
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalNonAssocRing
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalRing α] : NonUnitalRing (Shrink.{v} α) := (equivShrink α).symm.nonUnitalRing
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonAssocRing α] : NonAssocRing (Shrink.{v} α) := (equivShrink α).symm.nonAssocRing
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Ring α] : Ring (Shrink.{v} α) := (equivShrink α).symm.ring
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalCommRing α] : NonUnitalCommRing (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalCommRing
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommRing α] : CommRing (Shrink.{v} α) := (equivShrink α).symm.commRing
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring α] [IsDomain α] : IsDomain (Shrink.{v} α) := (Shrink.ringEquiv α).isDomain

end Shrink

