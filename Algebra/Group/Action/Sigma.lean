/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Data.Sigma.Basic

/-!
# Sigma instances for additive and multiplicative actions

This file defines instances for arbitrary sum of additive and multiplicative actions.

## See also

* `Mathlib/Algebra/Group/Action/Option.lean`
* `Mathlib/Algebra/Group/Action/Pi.lean`
* `Mathlib/Algebra/Group/Action/Prod.lean`
* `Mathlib/Algebra/Group/Action/Sum.lean`
-/

@[expose] public section

assert_not_exists MonoidWithZero


variable {ι : Type*} {M N : Type*} {α : ι → Type*}

namespace Sigma

section SMul

variable [∀ i, SMul M (α i)] [∀ i, SMul N (α i)] (a : M) (i : ι) (b : α i) (x : Σ i, α i)

@[to_additive Sigma.VAdd]
/-
**Sigma.** 是 Mathlib 中的一个实例，位于命名空间 `Sigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul M (Σ i, α i) :=
  ⟨fun a => (Sigma.map id) fun _ => (a • ·)⟩

@[to_additive]
/-
**Sigma.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：smul_def : a • x = x.map id fun _ => (a • ·)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_def : a • x = x.map id fun _ => (a • ·) :=
  rfl

@[to_additive (attr := simp)]
/-
**Sigma.smul_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：smul_mk : a • mk i b = ⟨i, a • b⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_mk : a • mk i b = ⟨i, a • b⟩ :=
  rfl

@[to_additive]
/-
**Sigma.instIsScalarTowerOfSMul** 是 Mathlib 中的一个实例，位于命名空间 `Sigma`。
形式化陈述：instIsScalarTowerOfSMul [SMul M N] [forall i, IsScalarTower M N (α i)] : I
sScalarTower M N (Σ i, α i)
参数：α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sigma.smul_mk`：smul_mk : a • mk i b = ⟨i, a • b⟩
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance instIsScalarTowerOfSMul [SMul M N] [∀ i, IsScalarTower M N (α i)] :
    IsScalarTower M N (Σ i, α i) :=
  ⟨fun a b x => by
    cases x
    rw [smul_mk, smul_mk, smul_mk, smul_assoc]⟩

@[to_additive]
/-
**Sigma.** 是 Mathlib 中的一个实例，位于命名空间 `Sigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, SMulCommClass M N (α i)] : SMulCommClass M N (Σ i, α i) :=
  ⟨fun a b x => by
    cases x
    rw [smul_mk, smul_mk, smul_mk, smul_mk, smul_comm]⟩

@[to_additive]
/-
**Sigma.** 是 Mathlib 中的一个实例，位于命名空间 `Sigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, SMul Mᵐᵒᵖ (α i)] [∀ i, IsCentralScalar M (α i)] : IsCentralScalar M (Σ i, α i) :=
  ⟨fun a x => by
    cases x
    rw [smul_mk, smul_mk, op_smul_eq_smul]⟩

/-- This is not an instance because `i` becomes a metavariable. -/
@[to_additive /-- This is not an instance because `i` becomes a metavariable. -/]
/-
**Sigma.FaithfulSMul'** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_2} {α : ι → Type u_4} [inst : (i : ι) → SMul 
M (α i)] (i : ι) [FaithfulSMul M (α i)],   FaithfulSMul M ((i : ι) × α i)
参数：i : ι；α i；i : ι；α i；(i : ι) × α i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `heq_iff_eq`：∀ {α : Sort u_1} {a b : α}, a ≍ b ↔ a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Sigma.ext_iff`：∀ {α : Type u} {β : α → Type v} {x y : Sigma β}, x = y ↔ 
x.fst = y.fst ∧ x.snd ≍ y.snd

--- 原说明 ---
This is not an instance because `i` becomes a metavariable.
-/
protected theorem FaithfulSMul' [FaithfulSMul M (α i)] : FaithfulSMul M (Σ i, α i) :=
  ⟨fun h => eq_of_smul_eq_smul fun a : α i => heq_iff_eq.1 (Sigma.ext_iff.1 <| h <| mk i a).2⟩

@[to_additive]
/-
**Sigma.** 是 Mathlib 中的一个实例，位于命名空间 `Sigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty ι] [∀ i, FaithfulSMul M (α i)] : FaithfulSMul M (Σ i, α i) :=
  (Nonempty.elim ‹_›) fun i => Sigma.FaithfulSMul' i

end SMul

@[to_additive]
/-
**Sigma.** 是 Mathlib 中的一个实例，位于命名空间 `Sigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {m : Monoid M} [∀ i, MulAction M (α i)] :
    MulAction M (Σ i, α i) where
  mul_smul a b x := by
    cases x
    rw [smul_mk, smul_mk, smul_mk, mul_smul]
  one_smul x := by
    cases x
    rw [smul_mk, one_smul]

end Sigma

