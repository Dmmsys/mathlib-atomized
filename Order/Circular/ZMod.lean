/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Oliver Nash, Yaël Dillies
-/
module

public import Mathlib.Order.Circular
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.ZMod.Defs

/-!
# The circular order on `ZMod n`

This file defines the circular order on `ZMod n`.
-/

public section

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CircularOrder ℤ := LinearOrder.toCircularOrder _

variable {a b c : ℤ}
/-
**Int.btw_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Int.btw_iff : btw a b c ↔ a <= b ∧ b <= c ∨ b <= c ∧ c <= a ∨ c <= a ∧ a <
= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Int.btw_iff : btw a b c ↔ a ≤ b ∧ b ≤ c ∨ b ≤ c ∧ c ≤ a ∨ c ≤ a ∧ a ≤ b := .rfl
/-
**Int.sbtw_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Int.sbtw_iff : sbtw a b c ↔ a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Int.sbtw_iff : sbtw a b c ↔ a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b := .rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) : CircularOrder (Fin n) := LinearOrder.toCircularOrder _

variable {n : ℕ} {a b c : Fin n}
/-
**Fin.btw_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Fin.btw_iff : btw a b c ↔ a <= b ∧ b <= c ∨ b <= c ∧ c <= a ∨ c <= a ∧ a <
= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Fin.btw_iff : btw a b c ↔ a ≤ b ∧ b ≤ c ∨ b ≤ c ∧ c ≤ a ∨ c ≤ a ∧ a ≤ b := .rfl
/-
**Fin.sbtw_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Fin.sbtw_iff : sbtw a b c ↔ a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Fin.sbtw_iff : sbtw a b c ↔ a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b := .rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ∀ (n : ℕ), CircularOrder (ZMod n)
  | 0 => inferInstanceAs <| CircularOrder ℤ
  | n + 1 => inferInstanceAs <| CircularOrder <| Fin <| n + 1
