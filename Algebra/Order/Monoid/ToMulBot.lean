/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

/-!
Making an additive monoid multiplicative then adding a zero is the same as adding a bottom
element then making it multiplicative.
-/

@[expose] public section


universe u

variable {α : Type u}

namespace WithZero

variable [Add α]

/-- Making an additive monoid multiplicative then adding a zero is the same as adding a bottom
element then making it multiplicative. -/
/-
**WithZero.toMulBot** 是 Mathlib 中的一个定义，位于命名空间 `WithZero`。
形式化陈述：toMulBot : WithZero (Multiplicative α) ≃* Multiplicative (WithBot α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Making an additive monoid multiplicative then adding a zero is the same as addin
g a bottom
element then making it multiplicative.
-/
def toMulBot : WithZero (Multiplicative α) ≃* Multiplicative (WithBot α) :=
  MulEquiv.refl _

@[simp]
/-
**WithZero.toMulBot_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：toMulBot_zero : toMulBot (0 : WithZero (Multiplicative α)) = Multiplicativ
e.ofAdd ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMulBot_zero : toMulBot (0 : WithZero (Multiplicative α)) = Multiplicative.ofAdd ⊥ :=
  rfl

@[simp]
/-
**WithZero.toMulBot_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：toMulBot_coe (x : Multiplicative α) : toMulBot ↑x = Multiplicative.ofAdd (
↑x.toAdd : WithBot α)
参数：x : Multiplicative α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMulBot_coe (x : Multiplicative α) :
    toMulBot ↑x = Multiplicative.ofAdd (↑x.toAdd : WithBot α) :=
  rfl

@[simp]
/-
**WithZero.toMulBot_symm_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：toMulBot_symm_bot : toMulBot.symm (Multiplicative.ofAdd (⊥ : WithBot α)) =
 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMulBot_symm_bot : toMulBot.symm (Multiplicative.ofAdd (⊥ : WithBot α)) = 0 :=
  rfl

@[simp]
/-
**WithZero.toMulBot_coe_ofAdd** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：toMulBot_coe_ofAdd (x : α) : toMulBot.symm (Multiplicative.ofAdd (x : With
Bot α)) = Multiplicative.ofAdd x
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMulBot_coe_ofAdd (x : α) :
    toMulBot.symm (Multiplicative.ofAdd (x : WithBot α)) = Multiplicative.ofAdd x :=
  rfl

variable [Preorder α] (a b : WithZero (Multiplicative α))
/-
**WithZero.toMulBot_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：toMulBot_strictMono : StrictMono (@toMulBot α _)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMulBot_strictMono : StrictMono (@toMulBot α _) := fun _ _ => id

@[simp]
/-
**WithZero.toMulBot_le** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：toMulBot_le : toMulBot a <= toMulBot b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toMulBot_le : toMulBot a ≤ toMulBot b ↔ a ≤ b :=
  Iff.rfl

@[simp]
/-
**WithZero.toMulBot_lt** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：toMulBot_lt : toMulBot a < toMulBot b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toMulBot_lt : toMulBot a < toMulBot b ↔ a < b :=
  Iff.rfl

end WithZero

