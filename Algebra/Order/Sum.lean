/-
Copyright (c) 2024 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
module

public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Order.Basic

/-!
# Interaction between `Sum.elim`, `≤`, and `0` or `1`

This file provides basic API for part-wise comparison of `Sum.elim` vectors against `0` or `1`.
-/

public section

namespace Sum

variable {α₁ α₂ β : Type*} [LE β] [One β] {v₁ : α₁ → β} {v₂ : α₂ → β}

@[to_additive]
/-
**Sum.one_le_elim_iff** 是 Mathlib 中的一个引理，位于命名空间 `Sum`。
形式化陈述：one_le_elim_iff : 1 <= Sum.elim v₁ v₂ ↔ 1 <= v₁ ∧ 1 <= v₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Sum.const_le_elim_iff`：const_le_elim_iff {b : β} {v₁ : α₁ -> β} {v₂ : α₂
 -> β} : Function.const _ b <= Sum.elim v₁ v₂ ↔ Function.const _ b <= v₁ ∧ Funct
ion.const _…
-/
lemma one_le_elim_iff : 1 ≤ Sum.elim v₁ v₂ ↔ 1 ≤ v₁ ∧ 1 ≤ v₂ :=
  const_le_elim_iff

@[to_additive]
/-
**Sum.elim_le_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Sum`。
形式化陈述：elim_le_one_iff : Sum.elim v₁ v₂ <= 1 ↔ v₁ <= 1 ∧ v₂ <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Sum.elim_le_const_iff`：elim_le_const_iff {b : β} {u₁ : α₁ -> β} {u₂ : α₂
 -> β} : Sum.elim u₁ u₂ <= Function.const _ b ↔ u₁ <= Function.const _ b ∧ u₂ <=
 Function.c…
-/
lemma elim_le_one_iff : Sum.elim v₁ v₂ ≤ 1 ↔ v₁ ≤ 1 ∧ v₂ ≤ 1 :=
  elim_le_const_iff

end Sum

