/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Action.TransferInstance
public import Mathlib.Logic.Small.Defs

/-!
# Transfer group structures from `α` to `Shrink α`
-/

@[expose] public noncomputable section

universe v
variable {M α : Type*} [Small.{v} α]

namespace Shrink

/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [One α] : One (Shrink.{v} α) := (equivShrink α).symm.one
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Mul α] : Mul (Shrink.{v} α) := (equivShrink α).symm.mul
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Div α] : Div (Shrink.{v} α) := (equivShrink α).symm.div
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Inv α] : Inv (Shrink.{v} α) := (equivShrink α).symm.Inv
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Pow α M] : Pow (Shrink.{v} α) M := (equivShrink α).symm.pow M

end Shrink

@[to_additive (attr := simp)]
/-
**equivShrink_symm_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：equivShrink_symm_one [One α] : (equivShrink α).symm 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
lemma equivShrink_symm_one [One α] : (equivShrink α).symm 1 = 1 :=
  (equivShrink α).symm_apply_apply 1

@[to_additive (attr := simp)]
/-
**equivShrink_symm_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：equivShrink_symm_mul [Mul α] (x y : Shrink α) : (equivShrink α).symm (x * 
y) = (equivShrink α).symm x * (equivShrink α).symm y
参数：x y : Shrink α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivShrink_symm_mul [Mul α] (x y : Shrink α) :
    (equivShrink α).symm (x * y) = (equivShrink α).symm x * (equivShrink α).symm y := by
  simp [Equiv.mul_def]

@[to_additive (attr := simp)]
/-
**equivShrink_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：equivShrink_mul [Mul α] (x y : α) : equivShrink α (x * y) = equivShrink α 
x * equivShrink α y
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivShrink_mul [Mul α] (x y : α) :
    equivShrink α (x * y) = equivShrink α x * equivShrink α y := by
  simp [Equiv.mul_def]

@[simp]
/-
**equivShrink_symm_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：equivShrink_symm_smul {M : Type*} [SMul M α] (m : M) (x : Shrink α) : (equ
ivShrink α).symm (m • x) = m • (equivShrink α).symm x
参数：m : M；x : Shrink α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivShrink_symm_smul {M : Type*} [SMul M α] (m : M) (x : Shrink α) :
    (equivShrink α).symm (m • x) = m • (equivShrink α).symm x := by
  simp [Equiv.smul_def]

@[simp]
/-
**equivShrink_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：equivShrink_smul {M : Type*} [SMul M α] (m : M) (x : α) : equivShrink α (m
 • x) = m • equivShrink α x
参数：m : M；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivShrink_smul {M : Type*} [SMul M α] (m : M) (x : α) :
    equivShrink α (m • x) = m • equivShrink α x := by
  simp [Equiv.smul_def]
@[to_additive (attr := simp)]
/-
**equivShrink_symm_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：equivShrink_symm_div [Div α] (x y : Shrink α) : (equivShrink α).symm (x / 
y) = (equivShrink α).symm x / (equivShrink α).symm y
参数：x y : Shrink α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivShrink_symm_div [Div α] (x y : Shrink α) :
    (equivShrink α).symm (x / y) = (equivShrink α).symm x / (equivShrink α).symm y := by
  simp [Equiv.div_def]

@[to_additive (attr := simp)]
/-
**equivShrink_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：equivShrink_div [Div α] (x y : α) : equivShrink α (x / y) = equivShrink α 
x / equivShrink α y
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivShrink_div [Div α] (x y : α) :
    equivShrink α (x / y) = equivShrink α x / equivShrink α y := by
  simp [Equiv.div_def]

@[to_additive (attr := simp)]
/-
**equivShrink_symm_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：equivShrink_symm_inv [Inv α] (x : Shrink α) : (equivShrink α).symm x⁻¹ = (
(equivShrink α).symm x)⁻¹
参数：x : Shrink α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivShrink_symm_inv [Inv α] (x : Shrink α) :
    (equivShrink α).symm x⁻¹ = ((equivShrink α).symm x)⁻¹ := by
  simp [Equiv.inv_def]

@[to_additive (attr := simp)]
/-
**equivShrink_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：equivShrink_inv [Inv α] (x : α) : equivShrink α x⁻¹ = (equivShrink α x)⁻¹
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivShrink_inv [Inv α] (x : α) : equivShrink α x⁻¹ = (equivShrink α x)⁻¹ := by
  simp [Equiv.inv_def]

namespace Shrink

/-- Shrink `α` to a smaller universe preserves multiplication. -/
@[to_additive /-- Shrink `α` to a smaller universe preserves addition. -/]
/-
**Shrink.mulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Shrink`。
形式化陈述：mulEquiv [Mul α] : Shrink.{v} α ≃* α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Shrink `α` to a smaller universe preserves multiplication.
-/
def mulEquiv [Mul α] : Shrink.{v} α ≃* α := (equivShrink α).symm.mulEquiv

@[to_additive]
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semigroup α] : Semigroup (Shrink.{v} α) := (equivShrink α).symm.semigroup

@[to_additive]
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommSemigroup α] : CommSemigroup (Shrink.{v} α) := (equivShrink α).symm.commSemigroup

@[to_additive]
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul α] [IsLeftCancelMul α] : IsLeftCancelMul (Shrink.{v} α) :=
  (equivShrink α).symm.isLeftCancelMul

@[to_additive]
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul α] [IsRightCancelMul α] : IsRightCancelMul (Shrink.{v} α) :=
  (equivShrink α).symm.isRightCancelMul

@[to_additive]
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul α] [IsCancelMul α] : IsCancelMul (Shrink.{v} α) := (equivShrink α).symm.isCancelMul

@[to_additive]
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulOneClass α] : MulOneClass (Shrink.{v} α) := (equivShrink α).symm.mulOneClass

@[to_additive]
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid α] : Monoid (Shrink.{v} α) := (equivShrink α).symm.monoid

@[to_additive]
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommMonoid α] : CommMonoid (Shrink.{v} α) := (equivShrink α).symm.commMonoid

@[to_additive]
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Group α] : Group (Shrink.{v} α) := (equivShrink α).symm.group

@[to_additive]
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommGroup α] : CommGroup (Shrink.{v} α) := (equivShrink α).symm.commGroup

@[to_additive]
/-
**Shrink.** 是 Mathlib 中的一个实例，位于命名空间 `Shrink`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid M] [MulAction M α] : MulAction M (Shrink.{v} α) := (equivShrink α).symm.mulAction M

end Shrink

