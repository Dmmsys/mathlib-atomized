/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Faithful

/-!
# Sum instances for additive and multiplicative actions

This file defines instances for additive and multiplicative actions on the binary `Sum` type.

## See also

* `Mathlib/Algebra/Group/Action/Option.lean`
* `Mathlib/Algebra/Group/Action/Pi.lean`
* `Mathlib/Algebra/Group/Action/Prod.lean`
* `Mathlib/Algebra/Group/Action/Sigma.lean`
-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {M N α β : Type*}

namespace Sum

section SMul

variable [SMul M α] [SMul M β] [SMul N α] [SMul N β] (a : M) (b : α) (c : β)
  (x : α ⊕ β)

@[to_additive]
/-
**Sum.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
形式化陈述：instSMul : SMul M (α oplus β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul : SMul M (α ⊕ β) :=
  ⟨fun a => Sum.map (a • ·) (a • ·)⟩

@[to_additive]
/-
**Sum.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：smul_def : a • x = x.map (a • ·) (a • ·)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_def : a • x = x.map (a • ·) (a • ·) :=
  rfl

@[to_additive (attr := simp)]
/-
**Sum.smul_inl** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：smul_inl : a • (inl b : α oplus β) = inl (a • b)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_inl : a • (inl b : α ⊕ β) = inl (a • b) :=
  rfl

@[to_additive (attr := simp)]
/-
**Sum.smul_inr** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：smul_inr : a • (inr c : α oplus β) = inr (a • c)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_inr : a • (inr c : α ⊕ β) = inr (a • c) :=
  rfl

@[to_additive (attr := simp)]
/-
**Sum.smul_swap** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：smul_swap : (a • x).swap = a • x.swap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem smul_swap : (a • x).swap = a • x.swap := by cases x <;> rfl
/-
**Sum.** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M N] [IsScalarTower M N α] [IsScalarTower M N β] : IsScalarTower M N (α ⊕ β) :=
  ⟨fun a b x => by
    cases x
    exacts [congr_arg inl (smul_assoc _ _ _), congr_arg inr (smul_assoc _ _ _)]⟩

@[to_additive]
/-
**Sum.** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulCommClass M N α] [SMulCommClass M N β] : SMulCommClass M N (α ⊕ β) :=
  ⟨fun a b x => by
    cases x
    exacts [congr_arg inl (smul_comm _ _ _), congr_arg inr (smul_comm _ _ _)]⟩

@[to_additive]
/-
**Sum.** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul Mᵐᵒᵖ α] [SMul Mᵐᵒᵖ β] [IsCentralScalar M α] [IsCentralScalar M β] :
    IsCentralScalar M (α ⊕ β) :=
  ⟨fun a x => by
    cases x
    exacts [congr_arg inl (op_smul_eq_smul _ _), congr_arg inr (op_smul_eq_smul _ _)]⟩

@[to_additive]
/-
**Sum.FaithfulSMulLeft** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
形式化陈述：FaithfulSMulLeft [FaithfulSMul M α] : FaithfulSMul M (α oplus β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
instance FaithfulSMulLeft [FaithfulSMul M α] : FaithfulSMul M (α ⊕ β) :=
  ⟨fun h => eq_of_smul_eq_smul fun a : α => by injection h (inl a)⟩

@[to_additive]
/-
**Sum.FaithfulSMulRight** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
形式化陈述：FaithfulSMulRight [FaithfulSMul M β] : FaithfulSMul M (α oplus β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
instance FaithfulSMulRight [FaithfulSMul M β] : FaithfulSMul M (α ⊕ β) :=
  ⟨fun h => eq_of_smul_eq_smul fun b : β => by injection h (inr b)⟩

end SMul

@[to_additive]
/-
**Sum.** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {m : Monoid M} [MulAction M α] [MulAction M β] :
    MulAction M (α ⊕ β) where
  mul_smul a b x := by
    cases x
    exacts [congr_arg inl (mul_smul _ _ _), congr_arg inr (mul_smul _ _ _)]
  one_smul x := by
    cases x
    exacts [congr_arg inl (one_smul _ _), congr_arg inr (one_smul _ _)]

end Sum

