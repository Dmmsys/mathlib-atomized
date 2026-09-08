/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.TransferInstance
public import Mathlib.Algebra.GroupWithZero.Action.Defs

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

public section

assert_not_exists Ring

variable {M M₀ A B : Type*}

namespace Equiv

variable (M) in
/-- Transfer `SMulZeroClass` across an `Equiv` -/
/-
**Equiv.smulZeroClass** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：(M : Type u_1) →   {A : Type u_3} → {B : Type u_4} → (e : A ≃ B) → [inst :
 Zero B] → [SMulZeroClass M B] → SMulZeroClass M A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `SMulZeroClass` across an `Equiv`
-/
protected abbrev smulZeroClass (e : A ≃ B) [Zero B] [SMulZeroClass M B] :
    letI := e.zero
    SMulZeroClass M A := by
  letI := e.zero
  exact {
    e.smul M with
    smul_zero := by simp [smul_def, zero_def]
  }

variable (M₀) in
/-- Transfer `SMulWithZero` across an `Equiv` -/
/-
**Equiv.smulWithZero** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：(M₀ : Type u_2) →   {A : Type u_3} →     {B : Type u_4} → (e : A ≃ B) → [i
nst : Zero M₀] → [inst_1 : Zero B] → [SMulWithZero M₀ B] → SMulWithZero M₀ A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `SMulWithZero` across an `Equiv`
-/
protected abbrev smulWithZero (e : A ≃ B) [Zero M₀] [Zero B] [SMulWithZero M₀ B] :
    letI := e.zero
    SMulWithZero M₀ A := by
  letI := e.zero
  exact {
    e.smulZeroClass M₀ with
    zero_smul := by simp [smul_def, zero_def]
  }

variable (M₀) in
/-- Transfer `MulActionWithZero` across an `Equiv` -/
/-
**Equiv.mulActionWithZero** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：(M₀ : Type u_2) →   {A : Type u_3} →     {B : Type u_4} →       (e : A ≃ B
) → [inst : MonoidWithZero M₀] → [inst_1 : Zero B] → [MulActionWithZero M₀ B] → 
MulActionWithZero M₀ A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `MulActionWithZero` across an `Equiv`
-/
protected abbrev mulActionWithZero (e : A ≃ B) [MonoidWithZero M₀] [Zero B]
    [MulActionWithZero M₀ B] :
    letI := e.zero
    MulActionWithZero M₀ A := by
  letI := e.zero
  exact { e.smulWithZero M₀, e.mulAction M₀ with }

variable (M) in
/-- Transfer `DistribSMul` across an `Equiv` -/
/-
**Equiv.distribSMul** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：(M : Type u_1) →   {A : Type u_3} → {B : Type u_4} → (e : A ≃ B) → [inst :
 AddZeroClass B] → [DistribSMul M B] → DistribSMul M A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `DistribSMul` across an `Equiv`
-/
protected abbrev distribSMul (e : A ≃ B) [AddZeroClass B] [DistribSMul M B] :
    letI := e.addZeroClass
    DistribSMul M A := by
  letI := e.addZeroClass
  exact {
    e.smulZeroClass M with
    smul_add := by simp [add_def, smul_def, smul_add]
  }

variable (M) in
/-- Transfer `DistribMulAction` across an `Equiv` -/
/-
**Equiv.distribMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：(M : Type u_1) →   {A : Type u_3} →     {B : Type u_4} →       (e : A ≃ B)
 → [inst : Monoid M] → [inst_1 : AddMonoid B] → [DistribMulAction M B] → Distrib
MulAction M A
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.one_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Monoid α} [
self : MulAction α β] (b : β), 1 • b = b

--- 原说明 ---
Transfer `DistribMulAction` across an `Equiv`
-/
protected abbrev distribMulAction (e : A ≃ B) [Monoid M] [AddMonoid B] [DistribMulAction M B] :
    letI := e.addMonoid
    DistribMulAction M A := by
  letI := e.addMonoid
  exact { e.distribSMul M, e.mulAction M with }

end Equiv

