/-
Copyright (c) 2016 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

import Mathlib.Tactic.ToDual

/-!
# Order definitions for propositions

This file defines orders on `Pi` and `Prop`.
-/

public section

/-
**Pi.hasLe** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.hasLe {ι : Type*} {π : ι -> Type*} [forall i, LE (π i)] : LE (forall i,
 π i) where le x y
参数：π i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.hasLe {ι : Type*} {π : ι → Type*} [∀ i, LE (π i)] : LE (∀ i, π i) where
  le x y := ∀ i, x i ≤ y i

@[to_dual self]
/-
**Pi.le_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.le_def {ι : Type*} {π : ι -> Type*} [forall i, LE (π i)] {x y : forall 
i, π i} : x <= y ↔ forall i, x i <= y i
参数：π i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Pi.le_def {ι : Type*} {π : ι → Type*} [∀ i, LE (π i)] {x y : ∀ i, π i} :
    x ≤ y ↔ ∀ i, x i ≤ y i :=
  .rfl

/-- Propositions form a complete Boolean algebra, where the `≤` relation is given by implication. -/
/-
**Prop.le** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prop.le : LE Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Propositions form a complete Boolean algebra, where the `≤` relation is given by
 implication.
-/
instance Prop.le : LE Prop :=
  ⟨(· → ·)⟩

@[simp]
/-
**le_Prop_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_Prop_eq : ((· <= ·) : Prop -> Prop -> Prop) = (· -> ·)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_Prop_eq : ((· ≤ ·) : Prop → Prop → Prop) = (· → ·) :=
  rfl
