/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Faithful

/-!
# Option instances for additive and multiplicative actions

This file defines instances for additive and multiplicative actions on `Option` type. Scalar
multiplication is defined by `a • some b = some (a • b)` and `a • none = none`.

## See also

* `Mathlib/Algebra/Group/Action/Pi.lean`
* `Mathlib/Algebra/Group/Action/Sigma.lean`
* `Mathlib/Algebra/Group/Action/Sum.lean`
-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {M N α : Type*}

namespace Option

section SMul

variable [SMul M α] [SMul N α] (a : M) (b : α) (x : Option α)

@[to_additive Option.VAdd]
/-
**Option.** 是 Mathlib 中的一个实例，位于命名空间 `Option`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul M (Option α) :=
  ⟨fun a => Option.map <| (a • ·)⟩

@[to_additive]
/-
**Option.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：smul_def : a • x = x.map (a • ·)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_def : a • x = x.map (a • ·) :=
  rfl

@[to_additive (attr := simp)]
/-
**Option.smul_none** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：smul_none : a • (none : Option α) = none
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_none : a • (none : Option α) = none :=
  rfl

@[to_additive (attr := simp)]
/-
**Option.smul_some** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：smul_some : a • some b = some (a • b)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_some : a • some b = some (a • b) :=
  rfl

@[to_additive]
/-
**Option.instIsScalarTowerOfSMul** 是 Mathlib 中的一个实例，位于命名空间 `Option`。
形式化陈述：instIsScalarTowerOfSMul [SMul M N] [IsScalarTower M N α] : IsScalarTower M
 N (Option α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance instIsScalarTowerOfSMul [SMul M N] [IsScalarTower M N α] : IsScalarTower M N (Option α) :=
  ⟨fun a b x => by
    cases x
    exacts [rfl, congr_arg some (smul_assoc _ _ _)]⟩

@[to_additive]
/-
**Option.** 是 Mathlib 中的一个实例，位于命名空间 `Option`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulCommClass M N α] : SMulCommClass M N (Option α) :=
  ⟨fun _ _ => Function.Commute.option_map <| smul_comm _ _⟩

@[to_additive]
/-
**Option.** 是 Mathlib 中的一个实例，位于命名空间 `Option`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] : IsCentralScalar M (Option α) :=
  ⟨fun a x => by
    cases x
    exacts [rfl, congr_arg some (op_smul_eq_smul _ _)]⟩

@[to_additive]
/-
**Option.** 是 Mathlib 中的一个实例，位于命名空间 `Option`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FaithfulSMul M α] : FaithfulSMul M (Option α) :=
  ⟨fun h => eq_of_smul_eq_smul fun b : α => by injection h (some b)⟩

end SMul

/-
**Option.** 是 Mathlib 中的一个实例，位于命名空间 `Option`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid M] [MulAction M α] :
    MulAction M (Option α) where
  one_smul b := by
    cases b
    exacts [rfl, congr_arg some (one_smul _ _)]
  mul_smul a₁ a₂ b := by
    cases b
    exacts [rfl, congr_arg some (mul_smul _ _ _)]

end Option

