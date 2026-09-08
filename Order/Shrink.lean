/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Order.SuccPred.Basic
public import Mathlib.Logic.Small.Defs

/-!
# Order instances on Shrink

If `α : Type v` is `u`-small, we transport various order related
instances on `α` to `Shrink.{u} α`.

-/

@[expose] public section

universe u

variable {α : Type*} [Small.{u} α]

section Bot
variable [Bot α]

@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Bot (Shrink.{u} α) where
  bot := equivShrink _ ⊥

@[to_dual (attr := simp)]
/-
**equivShrink_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：equivShrink_bot : equivShrink.{u} α ⊥ = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivShrink_bot : equivShrink.{u} α ⊥ = ⊥ := rfl

@[to_dual (attr := simp)]
/-
**equivShrink_symm_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：equivShrink_symm_bot : (equivShrink.{u} α).symm ⊥ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivShrink_symm_bot : (equivShrink.{u} α).symm ⊥ = ⊥ :=
  (equivShrink.{u} α).injective (by simp)

end Bot

section Preorder
variable [Preorder α]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Preorder (Shrink.{u} α) :=
  Preorder.lift (equivShrink α).symm

variable (α) in
/-- The order isomorphism `α ≃o Shrink.{u} α`. -/
/-
**orderIsoShrink** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：orderIsoShrink : α ≃o Shrink.{u} α where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order isomorphism `α ≃o Shrink.{u} α`.
-/
noncomputable def orderIsoShrink : α ≃o Shrink.{u} α where
  toEquiv := equivShrink α
  map_rel_iff' {a b} := by
    obtain ⟨a, rfl⟩ := (equivShrink.{u} α).symm.surjective a
    obtain ⟨b, rfl⟩ := (equivShrink.{u} α).symm.surjective b
    simp only [Equiv.apply_symm_apply]
    rfl

@[simp]
/-
**orderIsoShrink_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：orderIsoShrink_apply (a : α) : orderIsoShrink α a = equivShrink α a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma orderIsoShrink_apply (a : α) :
    orderIsoShrink α a = equivShrink α a := rfl

@[simp]
/-
**orderIsoShrink_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：orderIsoShrink_symm_apply (a : Shrink.{u} α) : (orderIsoShrink α).symm a =
 (equivShrink α).symm a
参数：a : Shrink.{u} α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma orderIsoShrink_symm_apply (a : Shrink.{u} α) :
    (orderIsoShrink α).symm a = (equivShrink α).symm a := rfl

@[simp]
/-
**equivShrink_le_equivShrink** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equivShrink_le_equivShrink {x y : α} : equivShrink α x <= equivShrink α y 
↔ x <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.map_rel_iff`：map_rel_iff (f : r ≃r s) {a b} : s (f a) (f b) ↔ r a
 b
-/
theorem equivShrink_le_equivShrink {x y : α} : equivShrink α x ≤ equivShrink α y ↔ x ≤ y :=
  (orderIsoShrink α).map_rel_iff

@[simp]
/-
**equivShrink_lt_equivShrink** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equivShrink_lt_equivShrink {x y : α} : equivShrink α x < equivShrink α y ↔
 x < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.map_rel_iff`：map_rel_iff (f : r ≃r s) {a b} : s (f a) (f b) ↔ r a
 b
-/
theorem equivShrink_lt_equivShrink {x y : α} : equivShrink α x < equivShrink α y ↔ x < y :=
  (orderIsoShrink α).toRelIsoLT.map_rel_iff

@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [OrderBot α] : OrderBot (Shrink.{u} α) where
  bot_le a := by simp [← (orderIsoShrink.{u} α).symm.le_iff_le]

@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [SuccOrder α] : SuccOrder (Shrink.{u} α) :=
  SuccOrder.ofOrderIso (orderIsoShrink.{u} α)

@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [WellFoundedLT α] : WellFoundedLT (Shrink.{u} α) where
  wf := (orderIsoShrink.{u} α).symm.toRelIsoLT.toRelEmbedding.isWellFounded.wf

end Preorder

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [PartialOrder α] : PartialOrder (Shrink.{u} α) :=
  (equivShrink _).symm.injective.partialOrder _ .rfl .rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [LinearOrder α] : LinearOrder (Shrink.{u} α) :=
  .lift' _ (equivShrink _).symm.injective
