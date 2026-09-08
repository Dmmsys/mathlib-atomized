/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Yuyang Zhao
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Tactic.Bound.Attribute
public import Mathlib.Tactic.Monotonicity.Attr

import Mathlib.Data.Set.Function
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Util.CompileInductive

/-!
# Lemmas on the monotone multiplication typeclasses

This file builds on `Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean` by proving several
lemmas that do not immediately follow from the typeclass specifications.
-/

public section

open Function

variable {α M₀ G₀ : Type*}

section MulZeroClass

variable [MulZeroClass α] {a b c d : α}

section Preorder

variable [Preorder α]

/-- Assumes left covariance. -/
/-
**Left.mul_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.mul_pos [PosMulStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b
参数：ha : 0 < a；hb : 0 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c

--- 原说明 ---
Assumes left covariance.
-/
theorem Left.mul_pos [PosMulStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha

alias mul_pos := Left.mul_pos
/-
**mul_neg_of_pos_of_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_neg_of_pos_of_neg [PosMulStrictMono α] (ha : 0 < a) (hb : b < 0) : a *
 b < 0
参数：ha : 0 < a；hb : b < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
-/
theorem mul_neg_of_pos_of_neg [PosMulStrictMono α] (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha

@[simp]
/-
**mul_pos_iff_of_pos_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_pos_iff_of_pos_left [PosMulStrictMono α] [PosMulReflectLT α] (h : 0 < 
a) : 0 < a * b ↔ 0 < b
参数：h : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_lt_mul_iff_right₀`：mul_lt_mul_iff_right₀ [PosMulStrictMono α] [PosMu
lReflectLT α] (a0 : 0 < a) : a * b < a * c ↔ b < c where mp h
-/
theorem mul_pos_iff_of_pos_left [PosMulStrictMono α] [PosMulReflectLT α] (h : 0 < a) :
    0 < a * b ↔ 0 < b := by simpa using mul_lt_mul_iff_right₀ (b := 0) h

/-- Assumes right covariance. -/
/-
**Right.mul_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.mul_pos [MulPosStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b
参数：ha : 0 < a；hb : 0 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a

--- 原说明 ---
Assumes right covariance.
-/
theorem Right.mul_pos [MulPosStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb
/-
**mul_neg_of_neg_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_neg_of_neg_of_pos [MulPosStrictMono α] (ha : a < 0) (hb : 0 < b) : a *
 b < 0
参数：ha : a < 0；hb : 0 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
-/
theorem mul_neg_of_neg_of_pos [MulPosStrictMono α] (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb

@[simp]
/-
**mul_pos_iff_of_pos_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_pos_iff_of_pos_right [MulPosStrictMono α] [MulPosReflectLT α] (h : 0 <
 b) : 0 < a * b ↔ 0 < a
参数：h : 0 < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mul_lt_mul_iff_left₀`：mul_lt_mul_iff_left₀ [MulPosStrictMono α] [MulPosR
eflectLT α] (a0 : 0 < a) : b * a < c * a ↔ b < c where mp h
-/
theorem mul_pos_iff_of_pos_right [MulPosStrictMono α] [MulPosReflectLT α] (h : 0 < b) :
    0 < a * b ↔ 0 < a := by simpa using mul_lt_mul_iff_left₀ (b := 0) h

/-- Assumes left covariance. -/
/-
**Left.mul_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.mul_nonneg [PosMulMono α] (ha : 0 <= a) (hb : 0 <= b) : 0 <= a * b
参数：ha : 0 <= a；hb : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c

--- 原说明 ---
Assumes left covariance.
-/
theorem Left.mul_nonneg [PosMulMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha

alias mul_nonneg := Left.mul_nonneg
/-
**mul_nonpos_of_nonneg_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_nonpos_of_nonneg_of_nonpos [PosMulMono α] (ha : 0 <= a) (hb : b <= 0) 
: a * b <= 0
参数：ha : 0 <= a；hb : b <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
-/
theorem mul_nonpos_of_nonneg_of_nonpos [PosMulMono α] (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha

/-- Assumes right covariance. -/
/-
**Right.mul_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.mul_nonneg [MulPosMono α] (ha : 0 <= a) (hb : 0 <= b) : 0 <= a * b
参数：ha : 0 <= a；hb : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a

--- 原说明 ---
Assumes right covariance.
-/
theorem Right.mul_nonneg [MulPosMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb
/-
**mul_nonpos_of_nonpos_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_nonpos_of_nonpos_of_nonneg [MulPosMono α] (ha : a <= 0) (hb : 0 <= b) 
: a * b <= 0
参数：ha : a <= 0；hb : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
-/
theorem mul_nonpos_of_nonpos_of_nonneg [MulPosMono α] (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 := by
  simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb
/-
**pos_of_mul_pos_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pos_of_mul_pos_right [PosMulReflectLT α] (h : 0 < a * b) (ha : 0 <= a) : 0
 < b
参数：h : 0 < a * b；ha : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_mul_lt_mul_left`：lt_of_mul_lt_mul_left [PosMulReflectLT α] (h : a 
* b < a * c) (a0 : 0 <= a) : b < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem pos_of_mul_pos_right [PosMulReflectLT α] (h : 0 < a * b) (ha : 0 ≤ a) : 0 < b :=
  lt_of_mul_lt_mul_left ((mul_zero a).symm ▸ h : a * 0 < a * b) ha
/-
**pos_of_mul_pos_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pos_of_mul_pos_left [MulPosReflectLT α] (h : 0 < a * b) (hb : 0 <= b) : 0 
< a
参数：h : 0 < a * b；hb : 0 <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_mul_lt_mul_right`：lt_of_mul_lt_mul_right [MulPosReflectLT α] (h : 
b * a < c * a) (a0 : 0 <= a) : b < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem pos_of_mul_pos_left [MulPosReflectLT α] (h : 0 < a * b) (hb : 0 ≤ b) : 0 < a :=
  lt_of_mul_lt_mul_right ((zero_mul b).symm ▸ h : 0 * b < a * b) hb
/-
**pos_iff_pos_of_mul_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pos_iff_pos_of_mul_pos [PosMulReflectLT α] [MulPosReflectLT α] (hab : 0 < 
a * b) : 0 < a ↔ 0 < b
参数：hab : 0 < a * b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pos_of_mul_pos_right`：pos_of_mul_pos_right [PosMulReflectLT α] (h : 0 < 
a * b) (ha : 0 <= a) : 0 < b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `pos_of_mul_pos_left`：pos_of_mul_pos_left [MulPosReflectLT α] (h : 0 < a 
* b) (hb : 0 <= b) : 0 < a
-/
theorem pos_iff_pos_of_mul_pos [PosMulReflectLT α] [MulPosReflectLT α] (hab : 0 < a * b) :
    0 < a ↔ 0 < b :=
  ⟨pos_of_mul_pos_right hab ∘ le_of_lt, pos_of_mul_pos_left hab ∘ le_of_lt⟩

/-- Assumes left strict covariance. -/
/-
**Left.mul_lt_mul_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.mul_lt_mul_of_nonneg [PosMulStrictMono α] [MulPosMono α] (h₁ : a < b)
 (h₂ : c < d) (a0 : 0 <= a) (c0 : 0 <= c) : a * c < b * d
参数：h₁ : a < b；h₂ : c < d；a0 : 0 <= a；c0 : 0 <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_of_le_of_lt_of_nonneg_of_pos`：mul_lt_mul_of_le_of_lt_of_nonne
g_of_pos [PosMulStrictMono α] [MulPosMono α] (h₁ : a <= b) (h₂ : c < d) (c0 : 0 
<= c) (b0 : 0 < b) : a * c < …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c

--- 原说明 ---
Assumes left strict covariance.
-/
theorem Left.mul_lt_mul_of_nonneg [PosMulStrictMono α] [MulPosMono α]
    (h₁ : a < b) (h₂ : c < d) (a0 : 0 ≤ a) (c0 : 0 ≤ c) : a * c < b * d :=
  mul_lt_mul_of_le_of_lt_of_nonneg_of_pos h₁.le h₂ c0 (a0.trans_lt h₁)

/-- Assumes right strict covariance. -/
/-
**Right.mul_lt_mul_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.mul_lt_mul_of_nonneg [PosMulMono α] [MulPosStrictMono α] (h₁ : a < b
) (h₂ : c < d) (a0 : 0 <= a) (c0 : 0 <= c) : a * c < b * d
参数：h₁ : a < b；h₂ : c < d；a0 : 0 <= a；c0 : 0 <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_of_lt_of_le_of_nonneg_of_pos`：mul_lt_mul_of_lt_of_le_of_nonne
g_of_pos [PosMulMono α] [MulPosStrictMono α] (h₁ : a < b) (h₂ : c <= d) (a0 : 0 
<= a) (d0 : 0 < d) : a * c < …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c

--- 原说明 ---
Assumes right strict covariance.
-/
theorem Right.mul_lt_mul_of_nonneg [PosMulMono α] [MulPosStrictMono α]
    (h₁ : a < b) (h₂ : c < d) (a0 : 0 ≤ a) (c0 : 0 ≤ c) : a * c < b * d :=
  mul_lt_mul_of_lt_of_le_of_nonneg_of_pos h₁ h₂.le a0 (c0.trans_lt h₂)

alias mul_lt_mul_of_nonneg := Left.mul_lt_mul_of_nonneg

alias mul_lt_mul'' := Left.mul_lt_mul_of_nonneg
attribute [gcongr] mul_lt_mul''
/-
**mul_self_le_mul_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_self_le_mul_self [PosMulMono α] [MulPosMono α] (ha : 0 <= a) (hab : a 
<= b) : a * a <= b * b
参数：ha : 0 <= a；hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem mul_self_le_mul_self [PosMulMono α] [MulPosMono α] (ha : 0 ≤ a) (hab : a ≤ b) :
    a * a ≤ b * b :=
  mul_le_mul hab hab ha <| ha.trans hab

end Preorder

section PartialOrder

/-- Local notation for the positive elements of a type `α`. -/
local notation3 "α>0" => { x : α // 0 < x }

variable [PartialOrder α]

/-
**posMulMono_iff_covariant_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：posMulMono_iff_covariant_pos : PosMulMono α ↔ CovariantClass α>0 α (fun x 
y => x * y) (· <= ·) where mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
-/
theorem posMulMono_iff_covariant_pos :
    PosMulMono α ↔ CovariantClass α>0 α (fun x y => x * y) (· ≤ ·) where
  mp _ := PosMulMono.to_covariantClass_pos_mul_le
  mpr h :=
    { mul_le_mul_of_nonneg_left a ha b c hbc := by
        obtain ha | ha := ha.eq_or_lt
        · simp [← ha]
        · exact @CovariantClass.elim α>0 α (fun x y => x * y) (· ≤ ·) _ ⟨_, ha⟩ _ _ hbc }
/-
**mulPosMono_iff_covariant_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulPosMono_iff_covariant_pos : MulPosMono α ↔ CovariantClass α>0 α (fun x 
y => y * x) (· <= ·) where mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
-/
theorem mulPosMono_iff_covariant_pos :
    MulPosMono α ↔ CovariantClass α>0 α (fun x y => y * x) (· ≤ ·) where
  mp _ := MulPosMono.to_covariantClass_pos_mul_le
  mpr h :=
    { mul_le_mul_of_nonneg_right a ha b c hbc := by
        obtain ha | ha := ha.eq_or_lt
        · simp [← ha]
        · exact @CovariantClass.elim α>0 α (fun x y => y * x) (· ≤ ·) _ ⟨_, ha⟩ _ _ hbc }
/-
**posMulReflectLT_iff_contravariant_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：posMulReflectLT_iff_contravariant_pos : PosMulReflectLT α ↔ ContravariantC
lass α>0 α (fun x y => x * y) (· < ·)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ContravariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N}
 {r : N → N → Prop} [self : ContravariantClass M N μ r],   Contravariant M N μ r
-/
theorem posMulReflectLT_iff_contravariant_pos :
    PosMulReflectLT α ↔ ContravariantClass α>0 α (fun x y => x * y) (· < ·) :=
  ⟨@PosMulReflectLT.to_contravariantClass_pos_mul_lt _ _ _ _, fun h =>
    { elim a b c h := by
        obtain ha | ha := a.prop.eq_or_lt
        · simp [← ha] at h
        · exact @ContravariantClass.elim α>0 α (fun x y => x * y) (· < ·) _ ⟨_, ha⟩ _ _ h }⟩
/-
**mulPosReflectLT_iff_contravariant_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulPosReflectLT_iff_contravariant_pos : MulPosReflectLT α ↔ ContravariantC
lass α>0 α (fun x y => y * x) (· < ·)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ContravariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N}
 {r : N → N → Prop} [self : ContravariantClass M N μ r],   Contravariant M N μ r
-/
theorem mulPosReflectLT_iff_contravariant_pos :
    MulPosReflectLT α ↔ ContravariantClass α>0 α (fun x y => y * x) (· < ·) :=
  ⟨@MulPosReflectLT.to_contravariantClass_pos_mul_lt _ _ _ _, fun h =>
    { elim a b c h := by
        obtain ha | ha := a.prop.eq_or_lt
        · simp [← ha] at h
        · exact @ContravariantClass.elim α>0 α (fun x y => y * x) (· < ·) _ ⟨_, ha⟩ _ _ h }⟩

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) PosMulStrictMono.toPosMulMono [PosMulStrictMono α] : PosMulMono α :=
  posMulMono_iff_covariant_pos.2 (covariantClass_le_of_lt _ _ _)

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MulPosStrictMono.toMulPosMono [MulPosStrictMono α] : MulPosMono α :=
  mulPosMono_iff_covariant_pos.2 (covariantClass_le_of_lt _ _ _)

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) PosMulReflectLE.toPosMulReflectLT [PosMulReflectLE α] :
    PosMulReflectLT α :=
  posMulReflectLT_iff_contravariant_pos.2
    ⟨fun a b c h =>
      (le_of_mul_le_mul_of_pos_left h.le a.2).lt_of_ne <| by
        rintro rfl
        simp at h⟩

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MulPosReflectLE.toMulPosReflectLT [MulPosReflectLE α] :
    MulPosReflectLT α :=
  mulPosReflectLT_iff_contravariant_pos.2
    ⟨fun a b c h =>
      (le_of_mul_le_mul_of_pos_right h.le a.2).lt_of_ne <| by
        rintro rfl
        simp at h⟩
/-
**mul_left_cancel_iff_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_left_cancel_iff_of_pos [PosMulReflectLE α] (a0 : 0 < a) : a * b = a * 
c ↔ b = c
参数：a0 : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `le_of_mul_le_mul_of_pos_left`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : 
Zero α] [inst_2 : Preorder α] {a b c : α} [PosMulReflectLE α],   a * b ≤ a * c →
 0 < a → b ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem mul_left_cancel_iff_of_pos [PosMulReflectLE α] (a0 : 0 < a) : a * b = a * c ↔ b = c :=
  ⟨fun h => (le_of_mul_le_mul_of_pos_left h.le a0).antisymm <|
    le_of_mul_le_mul_of_pos_left h.ge a0, congr_arg _⟩
/-
**mul_right_cancel_iff_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_right_cancel_iff_of_pos [MulPosReflectLE α] (b0 : 0 < b) : a * b = c *
 b ↔ a = c
参数：b0 : 0 < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `le_of_mul_le_mul_of_pos_right`：∀ {α : Type u_1} [inst : Mul α] [inst_1 :
 Zero α] [inst_2 : Preorder α] {a b c : α} [MulPosReflectLE α],   b * a ≤ c * a 
→ 0 < a → b ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem mul_right_cancel_iff_of_pos [MulPosReflectLE α] (b0 : 0 < b) : a * b = c * b ↔ a = c :=
  ⟨fun h => (le_of_mul_le_mul_of_pos_right h.le b0).antisymm <|
    le_of_mul_le_mul_of_pos_right h.ge b0, congr_arg (· * b)⟩
/-
**mul_eq_mul_iff_eq_and_eq_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_mul_iff_eq_and_eq_of_pos [PosMulStrictMono α] [MulPosStrictMono α] 
(hab : a <= b) (hcd : c <= d) (a0 : 0 < a) (d0 : 0 < d) : a * c = b * d ↔ a = b 
∧ c = d
参数：hab : a <= b；hcd : c <= d；a0 : 0 < a；d0 : 0 < d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.not_lt`：∀ {α : Type u_2} [inst : Preorder α] {a b : α}, a = b → ¬a < 
b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `MulPosStrictMono.toMulPosMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [MulPosStrictMono α], MulPosMono α
-/
theorem mul_eq_mul_iff_eq_and_eq_of_pos [PosMulStrictMono α] [MulPosStrictMono α]
    (hab : a ≤ b) (hcd : c ≤ d) (a0 : 0 < a) (d0 : 0 < d) :
    a * c = b * d ↔ a = b ∧ c = d := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, hab, hcd, true_and]
  refine ⟨fun hab ↦ h.not_lt ?_, fun hcd ↦ h.not_lt ?_⟩
  · exact (mul_le_mul_of_nonneg_left hcd a0.le).trans_lt (mul_lt_mul_of_pos_right hab d0)
  · exact (mul_lt_mul_of_pos_left hcd a0).trans_le (mul_le_mul_of_nonneg_right hab d0.le)
/-
**mul_eq_mul_iff_eq_and_eq_of_pos'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_mul_iff_eq_and_eq_of_pos' [PosMulStrictMono α] [MulPosStrictMono α]
 (hab : a <= b) (hcd : c <= d) (b0 : 0 < b) (c0 : 0 < c) : a * c = b * d ↔ a = b
 ∧ c = d
参数：hab : a <= b；hcd : c <= d；b0 : 0 < b；c0 : 0 < c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.not_lt`：∀ {α : Type u_2} [inst : Preorder α] {a b : α}, a = b → ¬a < 
b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `MulPosStrictMono.toMulPosMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [MulPosStrictMono α], MulPosMono α
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
-/
theorem mul_eq_mul_iff_eq_and_eq_of_pos' [PosMulStrictMono α] [MulPosStrictMono α]
    (hab : a ≤ b) (hcd : c ≤ d) (b0 : 0 < b) (c0 : 0 < c) :
    a * c = b * d ↔ a = b ∧ c = d := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, hab, hcd, true_and]
  refine ⟨fun hab ↦ h.not_lt ?_, fun hcd ↦ h.not_lt ?_⟩
  · exact (mul_lt_mul_of_pos_right hab c0).trans_le (mul_le_mul_of_nonneg_left hcd b0.le)
  · exact (mul_le_mul_of_nonneg_right hab c0.le).trans_lt (mul_lt_mul_of_pos_left hcd b0)
/-
**eq_and_eq_of_pos_of_le_of_mul_le_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_and_eq_of_pos_of_le_of_mul_le_mul [PosMulReflectLE α] [MulPosReflectLE 
α] [PosMulMono α] [MulPosMono α] (ha : 0 < a) (hc : 0 < c) (hab : a <= b) (hcd :
 c <= d) (h : b * d <= a * c) : a = b ∧ c = d
参数：ha : 0 < a；hc : 0 < c；hab : a <= b；hcd : c <= d；h : b * d <= a * c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_mul_le_mul_of_pos_right`：∀ {α : Type u_1} [inst : Mul α] [inst_1 :
 Zero α] [inst_2 : Preorder α] {a b c : α} [MulPosReflectLE α],   b * a ≤ c * a 
→ 0 < a → b ≤ c
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_of_mul_le_mul_of_pos_left`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : 
Zero α] [inst_2 : Preorder α] {a b c : α} [PosMulReflectLE α],   a * b ≤ a * c →
 0 < a → b ≤ c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
-/
theorem eq_and_eq_of_pos_of_le_of_mul_le_mul [PosMulReflectLE α] [MulPosReflectLE α]
    [PosMulMono α] [MulPosMono α] (ha : 0 < a) (hc : 0 < c) (hab : a ≤ b) (hcd : c ≤ d)
    (h : b * d ≤ a * c) : a = b ∧ c = d := by
  refine ⟨le_antisymm hab ?_, le_antisymm hcd ?_⟩
  · grw [hcd] at h
    · exact le_of_mul_le_mul_of_pos_right h <| hc.trans_le hcd
    · exact ha.le
  · grw [hab] at h
    · exact le_of_mul_le_mul_of_pos_left h <| ha.trans_le hab
    · exact hc.le

end PartialOrder

section LinearOrder

variable [LinearOrder α]

/-
**pos_and_pos_or_neg_and_neg_of_mul_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pos_and_pos_or_neg_and_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab :
 0 < a * b) : 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0
参数：hab : 0 < a * b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用引理 `lt_imp_lt_of_le_imp_le`：lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preo
rder β] {a b : α} {c d : β} (H : a <= b -> c <= d) (h : d < c) : b < a
· 使用定理 `mul_nonpos_of_nonpos_of_nonneg`：mul_nonpos_of_nonpos_of_nonneg [MulPosMo
no α] (ha : a <= 0) (hb : 0 <= b) : a * b <= 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_nonpos_of_nonneg_of_nonpos`：mul_nonpos_of_nonneg_of_nonpos [PosMulMo
no α] (ha : 0 <= a) (hb : b <= 0) : a * b <= 0
-/
theorem pos_and_pos_or_neg_and_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) :
    0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  rcases lt_trichotomy a 0 with (ha | rfl | ha)
  · refine Or.inr ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => ?_) hab⟩
    exact mul_nonpos_of_nonpos_of_nonneg ha.le hb
  · rw [zero_mul] at hab
    exact hab.false.elim
  · refine Or.inl ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => ?_) hab⟩
    exact mul_nonpos_of_nonneg_of_nonpos ha.le hb
/-
**neg_of_mul_pos_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_of_mul_pos_right [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : a
 <= 0) : b < 0
参数：h : 0 < a * b；ha : a <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `pos_and_pos_or_neg_and_neg_of_mul_pos`：pos_and_pos_or_neg_and_neg_of_mul
_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) : 0 < a ∧ 0 < b ∨ a < 0 ∧ b
 < 0
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem neg_of_mul_pos_right [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : a ≤ 0) : b < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.1.not_ge ha).2
/-
**neg_of_mul_pos_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_of_mul_pos_left [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : b 
<= 0) : a < 0
参数：h : 0 < a * b；ha : b <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `pos_and_pos_or_neg_and_neg_of_mul_pos`：pos_and_pos_or_neg_and_neg_of_mul
_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) : 0 < a ∧ 0 < b ∨ a < 0 ∧ b
 < 0
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem neg_of_mul_pos_left [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : b ≤ 0) : a < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.2.not_ge ha).1
/-
**neg_iff_neg_of_mul_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_iff_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) : a
 < 0 ↔ b < 0
参数：hab : 0 < a * b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_of_mul_pos_right`：neg_of_mul_pos_right [PosMulMono α] [MulPosMono α]
 (h : 0 < a * b) (ha : a <= 0) : b < 0
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `neg_of_mul_pos_left`：neg_of_mul_pos_left [PosMulMono α] [MulPosMono α] (
h : 0 < a * b) (ha : b <= 0) : a < 0
-/
theorem neg_iff_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) : a < 0 ↔ b < 0 :=
  ⟨neg_of_mul_pos_right hab ∘ le_of_lt, neg_of_mul_pos_left hab ∘ le_of_lt⟩
/-
**Left.neg_of_mul_neg_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.neg_of_mul_neg_right [PosMulMono α] (h : a * b < 0) (a0 : 0 <= a) : b
 < 0
参数：h : a * b < 0；a0 : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Left.mul_nonneg`：Left.mul_nonneg [PosMulMono α] (ha : 0 <= a) (hb : 0 <=
 b) : 0 <= a * b
-/
theorem Left.neg_of_mul_neg_right [PosMulMono α] (h : a * b < 0) (a0 : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun b0 : b ≥ 0 => (Left.mul_nonneg a0 b0).not_gt h

alias neg_of_mul_neg_right := Left.neg_of_mul_neg_right
/-
**Right.neg_of_mul_neg_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.neg_of_mul_neg_right [MulPosMono α] (h : a * b < 0) (a0 : 0 <= a) : 
b < 0
参数：h : a * b < 0；a0 : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Right.mul_nonneg`：Right.mul_nonneg [MulPosMono α] (ha : 0 <= a) (hb : 0 
<= b) : 0 <= a * b
-/
theorem Right.neg_of_mul_neg_right [MulPosMono α] (h : a * b < 0) (a0 : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun b0 : b ≥ 0 => (Right.mul_nonneg a0 b0).not_gt h
/-
**Left.neg_of_mul_neg_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.neg_of_mul_neg_left [PosMulMono α] (h : a * b < 0) (b0 : 0 <= b) : a 
< 0
参数：h : a * b < 0；b0 : 0 <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Left.mul_nonneg`：Left.mul_nonneg [PosMulMono α] (ha : 0 <= a) (hb : 0 <=
 b) : 0 <= a * b
-/
theorem Left.neg_of_mul_neg_left [PosMulMono α] (h : a * b < 0) (b0 : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun a0 : a ≥ 0 => (Left.mul_nonneg a0 b0).not_gt h

alias neg_of_mul_neg_left := Left.neg_of_mul_neg_left
/-
**Right.neg_of_mul_neg_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.neg_of_mul_neg_left [MulPosMono α] (h : a * b < 0) (b0 : 0 <= b) : a
 < 0
参数：h : a * b < 0；b0 : 0 <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Right.mul_nonneg`：Right.mul_nonneg [MulPosMono α] (ha : 0 <= a) (hb : 0 
<= b) : 0 <= a * b
-/
theorem Right.neg_of_mul_neg_left [MulPosMono α] (h : a * b < 0) (b0 : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun a0 : a ≥ 0 => (Right.mul_nonneg a0 b0).not_gt h

end LinearOrder

end MulZeroClass

section MulOneClass

variable [MulOneClass α] [Zero α] {a b c d : α}

section Preorder

variable [Preorder α]

/-! Lemmas of the form `a ≤ a * b ↔ 1 ≤ b` and `a * b ≤ a ↔ b ≤ 1`, assuming left covariance. -/

/-
**one_lt_of_lt_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_lt_of_lt_mul_left [MulRightReflectLT α] {a b : α} (h : b < a * b) : 1 
< a
参数：h : b < a * b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_mul_lt_mul_right'`：lt_of_mul_lt_mul_right' [i : MulRightReflectLT 
α] {a b c : α} (bc : b * a < c * a) : b < c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
Lemmas of the form `a ≤ a * b ↔ 1 ≤ b` and `a * b ≤ a ↔ b ≤ 1`, assuming left co
variance.
-/
lemma one_lt_of_lt_mul_left₀ [PosMulReflectLT α] (ha : 0 ≤ a) (h : a < a * b) : 1 < b :=
  lt_of_mul_lt_mul_left (by simpa) ha
/-
**one_lt_of_lt_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_lt_of_lt_mul_right [MulLeftReflectLT α] {a b : α} (h : a < a * b) : 1 
< b
参数：h : a < a * b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_mul_lt_mul_left'`：lt_of_mul_lt_mul_left' [MulLeftReflectLT α] {a b
 c : α} (bc : a * b < a * c) : b < c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma one_lt_of_lt_mul_right₀ [MulPosReflectLT α] (hb : 0 ≤ b) (h : b < a * b) : 1 < a :=
  lt_of_mul_lt_mul_right (by simpa) hb
/-
**one_le_of_le_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_le_of_le_mul_left [MulRightReflectLE α] {a b : α} (h : b <= a * b) : 1
 <= a
参数：h : b <= a * b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_mul_le_mul_right'`：le_of_mul_le_mul_right' [MulRightReflectLE α] {
a b c : α} (bc : b * a <= c * a) : b <= c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma one_le_of_le_mul_left₀ [PosMulReflectLE α] (ha : 0 < a) (h : a ≤ a * b) : 1 ≤ b :=
  le_of_mul_le_mul_left (by simpa) ha
/-
**one_le_of_le_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_le_of_le_mul_right [MulLeftReflectLE α] {a b : α} (h : a <= a * b) : 1
 <= b
参数：h : a <= a * b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_mul_le_mul_left'`：le_of_mul_le_mul_left' [MulLeftReflectLE α] {a b
 c : α} (bc : a * b <= a * c) : b <= c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma one_le_of_le_mul_right₀ [MulPosReflectLE α] (hb : 0 < b) (h : b ≤ a * b) : 1 ≤ a :=
  le_of_mul_le_mul_right (by simpa) hb

@[simp]
/-
**le_mul_iff_one_le_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_mul_iff_one_le_right [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) : 
a <= a * b ↔ 1 <= b
参数：a0 : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `mul_le_mul_iff_right₀`：mul_le_mul_iff_right₀ [PosMulMono α] [PosMulRefle
ctLE α] (a0 : 0 < a) : a * b <= a * c ↔ b <= c
-/
lemma le_mul_iff_one_le_right [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) : a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_iff_right₀ a0)

@[simp]
/-
**lt_mul_iff_one_lt_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_mul_iff_one_lt_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 <
 a) : a < a * b ↔ 1 < b
参数：a0 : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `mul_lt_mul_iff_right₀`：mul_lt_mul_iff_right₀ [PosMulStrictMono α] [PosMu
lReflectLT α] (a0 : 0 < a) : a * b < a * c ↔ b < c where mp h
-/
theorem lt_mul_iff_one_lt_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a < a * b ↔ 1 < b :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_right₀ a0)

@[simp]
/-
**mul_le_iff_le_one_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_le_iff_le_one_right [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) : 
a * b <= a ↔ b <= 1
参数：a0 : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `mul_le_mul_iff_right₀`：mul_le_mul_iff_right₀ [PosMulMono α] [PosMulRefle
ctLE α] (a0 : 0 < a) : a * b <= a * c ↔ b <= c
-/
lemma mul_le_iff_le_one_right [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) : a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_iff_right₀ a0)

@[simp]
/-
**mul_lt_iff_lt_one_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_iff_lt_one_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 <
 a) : a * b < a ↔ b < 1
参数：a0 : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `mul_lt_mul_iff_right₀`：mul_lt_mul_iff_right₀ [PosMulStrictMono α] [PosMu
lReflectLT α] (a0 : 0 < a) : a * b < a * c ↔ b < c where mp h
-/
theorem mul_lt_iff_lt_one_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a * b < a ↔ b < 1 :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_right₀ a0)

/-! Lemmas of the form `a ≤ b * a ↔ 1 ≤ b` and `a * b ≤ b ↔ a ≤ 1`, assuming right covariance. -/

@[simp]
/-
**le_mul_iff_one_le_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_mul_iff_one_le_left [MulPosMono α] [MulPosReflectLE α] (a0 : 0 < a) : a
 <= b * a ↔ 1 <= b
参数：a0 : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `mul_le_mul_iff_left₀`：mul_le_mul_iff_left₀ [MulPosMono α] [MulPosReflect
LE α] (a0 : 0 < a) : b * a <= c * a ↔ b <= c

--- 原说明 ---
Lemmas of the form `a ≤ b * a ↔ 1 ≤ b` and `a * b ≤ b ↔ a ≤ 1`, assuming right c
ovariance.
-/
lemma le_mul_iff_one_le_left [MulPosMono α] [MulPosReflectLE α] (a0 : 0 < a) : a ≤ b * a ↔ 1 ≤ b :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_iff_left₀ a0)

@[simp]
/-
**lt_mul_iff_one_lt_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_mul_iff_one_lt_left [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < 
a) : a < b * a ↔ 1 < b
参数：a0 : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `mul_lt_mul_iff_left₀`：mul_lt_mul_iff_left₀ [MulPosStrictMono α] [MulPosR
eflectLT α] (a0 : 0 < a) : b * a < c * a ↔ b < c where mp h
-/
theorem lt_mul_iff_one_lt_left [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a) :
    a < b * a ↔ 1 < b :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_left₀ a0)

@[simp]
/-
**mul_le_iff_le_one_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_le_iff_le_one_left [MulPosMono α] [MulPosReflectLE α] (b0 : 0 < b) : a
 * b <= b ↔ a <= 1
参数：b0 : 0 < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `mul_le_mul_iff_left₀`：mul_le_mul_iff_left₀ [MulPosMono α] [MulPosReflect
LE α] (a0 : 0 < a) : b * a <= c * a ↔ b <= c
-/
lemma mul_le_iff_le_one_left [MulPosMono α] [MulPosReflectLE α] (b0 : 0 < b) : a * b ≤ b ↔ a ≤ 1 :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_iff_left₀ b0)

@[simp]
/-
**mul_lt_iff_lt_one_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_iff_lt_one_left [MulPosStrictMono α] [MulPosReflectLT α] (b0 : 0 < 
b) : a * b < b ↔ a < 1
参数：b0 : 0 < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `mul_lt_mul_iff_left₀`：mul_lt_mul_iff_left₀ [MulPosStrictMono α] [MulPosR
eflectLT α] (a0 : 0 < a) : b * a < c * a ↔ b < c where mp h
-/
theorem mul_lt_iff_lt_one_left [MulPosStrictMono α] [MulPosReflectLT α] (b0 : 0 < b) :
    a * b < b ↔ a < 1 :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_left₀ b0)

/-! Lemmas of the form `1 ≤ b → a ≤ a * b`.

Variants with `< 0` and `≤ 0` instead of `0 <` and `0 ≤` appear in `Mathlib/Algebra/Order/Ring/Defs`
(which imports this file) as they need additional results which are not yet available here. -/

/-
**mul_le_of_le_one_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b) (h : a <= 1) : a * b <=
 b
参数：hb : 0 <= b；h : a <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a

--- 原说明 ---
Lemmas of the form `1 ≤ b → a ≤ a * b`.

Variants with `< 0` and `≤ 0` instead of `0 <` and `0 ≤` appear in `Mathlib/Alge
bra/Order/Ring/Defs`
(which imports this file) as they need additional results which are not yet avai
lable here.
-/
theorem mul_le_of_le_one_left [MulPosMono α] (hb : 0 ≤ b) (h : a ≤ 1) : a * b ≤ b := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb
/-
**le_mul_of_one_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_mul_of_one_le_left [MulPosMono α] (hb : 0 <= b) (h : 1 <= a) : b <= a *
 b
参数：hb : 0 <= b；h : 1 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
-/
theorem le_mul_of_one_le_left [MulPosMono α] (hb : 0 ≤ b) (h : 1 ≤ a) : b ≤ a * b := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb
/-
**mul_le_of_le_one_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_of_le_one_right [PosMulMono α] (ha : 0 <= a) (h : b <= 1) : a * b <
= a
参数：ha : 0 <= a；h : b <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
-/
theorem mul_le_of_le_one_right [PosMulMono α] (ha : 0 ≤ a) (h : b ≤ 1) : a * b ≤ a := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha
/-
**le_mul_of_one_le_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_mul_of_one_le_right [PosMulMono α] (ha : 0 <= a) (h : 1 <= b) : a <= a 
* b
参数：ha : 0 <= a；h : 1 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
-/
theorem le_mul_of_one_le_right [PosMulMono α] (ha : 0 ≤ a) (h : 1 ≤ b) : a ≤ a * b := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha
/-
**mul_lt_of_lt_one_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_of_lt_one_left [MulPosStrictMono α] (hb : 0 < b) (h : a < 1) : a * 
b < b
参数：hb : 0 < b；h : a < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
-/
theorem mul_lt_of_lt_one_left [MulPosStrictMono α] (hb : 0 < b) (h : a < 1) : a * b < b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb
/-
**lt_mul_of_one_lt_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_mul_of_one_lt_left [MulPosStrictMono α] (hb : 0 < b) (h : 1 < a) : b < 
a * b
参数：hb : 0 < b；h : 1 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
-/
theorem lt_mul_of_one_lt_left [MulPosStrictMono α] (hb : 0 < b) (h : 1 < a) : b < a * b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb
/-
**mul_lt_of_lt_one_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_of_lt_one_right [PosMulStrictMono α] (ha : 0 < a) (h : b < 1) : a *
 b < a
参数：ha : 0 < a；h : b < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
-/
theorem mul_lt_of_lt_one_right [PosMulStrictMono α] (ha : 0 < a) (h : b < 1) : a * b < a := by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha
/-
**lt_mul_of_one_lt_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_mul_of_one_lt_right [PosMulStrictMono α] (ha : 0 < a) (h : 1 < b) : a <
 a * b
参数：ha : 0 < a；h : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
-/
theorem lt_mul_of_one_lt_right [PosMulStrictMono α] (ha : 0 < a) (h : 1 < b) : a < a * b := by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha

end Preorder

end MulOneClass

section MulZero

variable [Mul M₀] [Zero M₀] [Preorder M₀] [Preorder α] {f g : α → M₀}

/-
**Monotone.mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.mul [PosMulMono M₀] [MulPosMono M₀] (hf : Monotone f) (hg : Monot
one g) (hf₀ : forall x, 0 <= f x) (hg₀ : forall x, 0 <= g x) : Monotone (f * g)
参数：hf : Monotone f；hg : Monotone g；hf₀ : forall x, 0 <= f x；hg₀ : forall x, 0 <=
 g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
-/
lemma Monotone.mul [PosMulMono M₀] [MulPosMono M₀] (hf : Monotone f) (hg : Monotone g)
    (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 ≤ g x) : Monotone (f * g) :=
  fun _ _ h ↦ mul_le_mul (hf h) (hg h) (hg₀ _) (hf₀ _)
/-
**MonotoneOn.mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonotoneOn.mul [PosMulMono M₀] [MulPosMono M₀] {s : Set α} (hf : MonotoneO
n f s) (hg : MonotoneOn g s) (hf₀ : forall x in s, 0 <= f x) (hg₀ : forall x in 
s, 0 <= g x) : MonotoneOn (f * g) s
参数：hf : MonotoneOn f s；hg : MonotoneOn g s；hf₀ : forall x in s, 0 <= f x；hg₀ : f
orall x in s, 0 <= g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
-/
lemma MonotoneOn.mul [PosMulMono M₀] [MulPosMono M₀] {s : Set α} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) (hf₀ : ∀ x ∈ s, 0 ≤ f x) (hg₀ : ∀ x ∈ s, 0 ≤ g x) :
    MonotoneOn (f * g) s :=
  fun _ ha _ hb h ↦ mul_le_mul (hf ha hb h) (hg ha hb h) (hg₀ _ ha) (hf₀ _ hb)

end MulZero

section MonoidWithZero
variable [MonoidWithZero M₀]

section Preorder
variable [Preorder M₀] {a b : M₀} {m n : ℕ}

/-
**pow_succ_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a : M
₀} [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a ^ (n + 1)
参数：n : ℕ；n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pow_succ_nonneg [PosMulMono M₀] (ha : 0 ≤ a) : ∀ n, 0 ≤ a ^ (n + 1)
  | 0 => (pow_one a).symm ▸ ha
  | _ + 1 => pow_succ a _ ▸ mul_nonneg (pow_succ_nonneg ha _) ha
/-
**pow_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a : M
₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a ^ n
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pow_nonneg [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 0 ≤ a) : ∀ n, 0 ≤ a ^ n
  | 0 => pow_zero a ▸ zero_le_one
  | n + 1 => pow_succ a n ▸ mul_nonneg (pow_nonneg ha _) ha
/-
**zero_pow_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] [ZeroL
EOneClass M₀] (n : ℕ), 0 ^ n ≤ 1
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
lemma zero_pow_le_one [ZeroLEOneClass M₀] : ∀ n : ℕ, (0 : M₀) ^ n ≤ 1
  | 0 => (pow_zero _).le
  | n + 1 => by rw [zero_pow n.succ_ne_zero]; exact zero_le_one
/-
**pow_right_anti** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_right_anti₀ [PosMulMono M₀] (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) : Antitone (fun n : ℕ ↦ a ^ n) :=
  antitone_nat_of_succ_le fun n ↦ by
    have : ZeroLEOneClass M₀ := ⟨ha₀.trans ha₁⟩
    rw [← mul_one (a ^ n), pow_succ]
    gcongr
    exact pow_nonneg ha₀ n
/-
**pow_le_pow_of_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_le_pow_of_le_one [PosMulMono M₀] (ha₀ : 0 <= a) (ha₁ : a <= 1) {m n : 
Nat} (hmn : m <= n) : a ^ n <= a ^ m
参数：ha₀ : 0 <= a；ha₁ : a <= 1；hmn : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pow_right_anti₀`：pow_right_anti₀ [PosMulMono M₀] (ha₀ : 0 <= a) (ha₁ : a
 <= 1) : Antitone (fun n : Nat => a ^ n)
-/
lemma pow_le_pow_of_le_one [PosMulMono M₀] (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) {m n : ℕ}
    (hmn : m ≤ n) : a ^ n ≤ a ^ m := pow_right_anti₀ ha₀ ha₁ hmn
/-
**pow_le_of_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_le_of_le_one [PosMulMono M₀] (h₀ : 0 <= a) (h₁ : a <= 1) (hn : n != 0)
 : a ^ n <= a
参数：h₀ : 0 <= a；h₁ : a <= 1；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `pow_le_pow_of_le_one`：pow_le_pow_of_le_one [PosMulMono M₀] (ha₀ : 0 <= a
) (ha₁ : a <= 1) {m n : Nat} (hmn : m <= n) : a ^ n <= a ^ m
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
-/
lemma pow_le_of_le_one [PosMulMono M₀] (h₀ : 0 ≤ a) (h₁ : a ≤ 1) (hn : n ≠ 0) : a ^ n ≤ a :=
  (pow_one a).subst (pow_le_pow_of_le_one h₀ h₁ (Nat.pos_of_ne_zero hn))
/-
**sq_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sq_le [PosMulMono M₀] (h₀ : 0 <= a) (h₁ : a <= 1) : a ^ 2 <= a
参数：h₀ : 0 <= a；h₁ : a <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pow_le_of_le_one`：pow_le_of_le_one [PosMulMono M₀] (h₀ : 0 <= a) (h₁ : a
 <= 1) (hn : n != 0) : a ^ n <= a
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma sq_le [PosMulMono M₀] (h₀ : 0 ≤ a) (h₁ : a ≤ 1) : a ^ 2 ≤ a :=
  pow_le_of_le_one h₀ h₁ two_ne_zero
/-
**pow_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_le_one₀ [PosMulMono M₀] {n : ℕ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) : a ^ n ≤ 1 :=
  pow_zero a ▸ pow_right_anti₀ ha₀ ha₁ (Nat.zero_le n)
/-
**one_le_mul_of_one_le_of_one_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_le_mul_of_one_le_of_one_le [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1
 <= a) (hb : 1 <= b) : (1 : M₀) <= a * b
参数：ha : 1 <= a；hb : 1 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_mul_of_one_le_right`：le_mul_of_one_le_right [PosMulMono α] (ha : 0 <=
 a) (h : 1 <= b) : a <= a * b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
lemma one_le_mul_of_one_le_of_one_le [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (1 : M₀) ≤ a * b := ha.trans <| le_mul_of_one_le_right (zero_le_one.trans ha) hb
/-
**one_lt_mul_of_le_of_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_lt_mul_of_le_of_lt [ZeroLEOneClass M₀] [MulPosMono M₀] (ha : 1 <= a) (
hb : 1 < b) : 1 < a * b
参数：ha : 1 <= a；hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_mul_of_one_le_left`：le_mul_of_one_le_left [MulPosMono α] (hb : 0 <= b
) (h : 1 <= a) : b <= a * b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma one_lt_mul_of_le_of_lt [ZeroLEOneClass M₀] [MulPosMono M₀] (ha : 1 ≤ a) (hb : 1 < b) :
    1 < a * b := hb.trans_le <| le_mul_of_one_le_left (zero_le_one.trans hb.le) ha
/-
**one_lt_mul_of_lt_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_lt_mul_of_lt_of_le [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 < a) (h
b : 1 <= b) : 1 < a * b
参数：ha : 1 < a；hb : 1 <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_mul_of_one_le_right`：le_mul_of_one_le_right [PosMulMono α] (ha : 0 <=
 a) (h : 1 <= b) : a <= a * b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma one_lt_mul_of_lt_of_le [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 < a) (hb : 1 ≤ b) :
    1 < a * b := ha.trans_le <| le_mul_of_one_le_right (zero_le_one.trans ha.le) hb

alias one_lt_mul := one_lt_mul_of_le_of_lt
/-
**mul_lt_one_of_nonneg_of_lt_one_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_lt_one_of_nonneg_of_lt_one_left [PosMulMono M₀] (ha₀ : 0 <= a) (ha : a
 < 1) (hb : b <= 1) : a * b < 1
参数：ha₀ : 0 <= a；ha : a < 1；hb : b <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `mul_le_of_le_one_right`：mul_le_of_le_one_right [PosMulMono α] (ha : 0 <=
 a) (h : b <= 1) : a * b <= a
-/
lemma mul_lt_one_of_nonneg_of_lt_one_left [PosMulMono M₀] (ha₀ : 0 ≤ a) (ha : a < 1) (hb : b ≤ 1) :
    a * b < 1 := (mul_le_of_le_one_right ha₀ hb).trans_lt ha
/-
**mul_lt_one_of_nonneg_of_lt_one_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_lt_one_of_nonneg_of_lt_one_right [MulPosMono M₀] (ha : a <= 1) (hb₀ : 
0 <= b) (hb : b < 1) : a * b < 1
参数：ha : a <= 1；hb₀ : 0 <= b；hb : b < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `mul_le_of_le_one_left`：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b
) (h : a <= 1) : a * b <= b
-/
lemma mul_lt_one_of_nonneg_of_lt_one_right [MulPosMono M₀] (ha : a ≤ 1) (hb₀ : 0 ≤ b) (hb : b < 1) :
    a * b < 1 := (mul_le_of_le_one_left hb₀ ha).trans_lt hb

@[bound]
/-
**Bound.one_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 `Bound`。
形式化陈述：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preorder M₀] {a b :
 M₀} [ZeroLEOneClass M₀] [PosMulMono M₀]   [MulPosMono M₀], 1 ≤ a ∧ 1 < b ∨ 1 < 
a ∧ 1 ≤ b → 1 < a * b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_lt_mul`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a b : M₀} [ZeroLEOneClass M₀] [MulPosMono M₀],   1 ≤ a → 1 < b → 1 < a 
…
· 使用引理 `one_lt_mul_of_lt_of_le`：one_lt_mul_of_lt_of_le [ZeroLEOneClass M₀] [PosM
ulMono M₀] (ha : 1 < a) (hb : 1 <= b) : 1 < a * b
-/
protected lemma Bound.one_lt_mul [ZeroLEOneClass M₀] [PosMulMono M₀] [MulPosMono M₀] :
    1 ≤ a ∧ 1 < b ∨ 1 < a ∧ 1 ≤ b → 1 < a * b := by
  rintro (⟨ha, hb⟩ | ⟨ha, hb⟩); exacts [one_lt_mul ha hb, one_lt_mul_of_lt_of_le ha hb]

@[bound]
/-
**mul_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_le_one₀ [MulPosMono M₀] (ha : a ≤ 1) (hb₀ : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
  (mul_le_mul_of_nonneg_right ha hb₀).trans <| by rwa [one_mul]
/-
**pow_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_lt_one₀ [PosMulMono M₀] (h₀ : 0 ≤ a) (h₁ : a < 1) : ∀ {n : ℕ}, n ≠ 0 → a ^ n < 1
  | 0, h => (h rfl).elim
  | n + 1, _ => by
    rw [pow_succ']; exact mul_lt_one_of_nonneg_of_lt_one_left h₀ h₁ (pow_le_one₀ h₀ h₁.le)
/-
**pow_right_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_right_mono₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (h : 1 ≤ a) : Monotone (a ^ ·) :=
  monotone_nat_of_le_succ fun n => by
    rw [pow_succ]; exact le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans h) _) h
/-
**one_le_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_le_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) {n : ℕ} : 1 ≤ a ^ n :=
  pow_zero a ▸ pow_right_mono₀ ha n.zero_le
/-
**one_lt_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_lt_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 < a) : ∀ {n : ℕ}, n ≠ 0 → 1 < a ^ n
  | 0, h => (h rfl).elim
  | n + 1, _ => by rw [pow_succ']; exact one_lt_mul_of_lt_of_le ha (one_le_pow₀ ha.le)

/-- `bound` lemma for branching on `1 ≤ a ∨ a ≤ 1` when proving `a ^ n ≤ a ^ m` -/
@[bound]
/-
**Bound.pow_le_pow_right_of_le_one_or_one_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Bound.pow_le_pow_right_of_le_one_or_one_le [ZeroLEOneClass M₀] [PosMulMono
 M₀] (h : 1 <= a ∧ n <= m ∨ 0 <= a ∧ a <= 1 ∧ m <= n) : a ^ n <= a ^ m
参数：h : 1 <= a ∧ n <= m ∨ 0 <= a ∧ a <= 1 ∧ m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pow_right_mono₀`：pow_right_mono₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (h 
: 1 <= a) : Monotone (a ^ ·)
· 使用引理 `pow_le_pow_of_le_one`：pow_le_pow_of_le_one [PosMulMono M₀] (ha₀ : 0 <= a
) (ha₁ : a <= 1) {m n : Nat} (hmn : m <= n) : a ^ n <= a ^ m

--- 原说明 ---
`bound` lemma for branching on `1 ≤ a ∨ a ≤ 1` when proving `a ^ n ≤ a ^ m`
-/
lemma Bound.pow_le_pow_right_of_le_one_or_one_le [ZeroLEOneClass M₀] [PosMulMono M₀]
    (h : 1 ≤ a ∧ n ≤ m ∨ 0 ≤ a ∧ a ≤ 1 ∧ m ≤ n) :
    a ^ n ≤ a ^ m := by
  obtain ⟨a1, nm⟩ | ⟨a0, a1, mn⟩ := h
  · exact pow_right_mono₀ a1 nm
  · exact pow_le_pow_of_le_one a0 a1 mn

@[gcongr]
/-
**pow_le_pow_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_le_pow_right₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) (hmn : m ≤ n) :
    a ^ m ≤ a ^ n :=
  pow_right_mono₀ ha hmn
/-
**le_self_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_self_pow (ha : 1 <= a) (hn : n != 0) : a <= a ^ n
参数：ha : 1 <= a；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `pow_le_pow_right'`：pow_le_pow_right' {n m : Nat} (ha : 1 <= a) (h : n <=
 m) : a ^ n <= a ^ m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
-/
lemma le_self_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) (hn : n ≠ 0) : a ≤ a ^ n := by
  simpa only [pow_one] using pow_le_pow_right₀ ha <| Nat.pos_iff_ne_zero.2 hn

/-- The `bound` tactic can't handle `m ≠ 0` goals yet, so we express as `0 < m` -/
@[bound]
/-
**Bound.le_self_pow_of_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Bound.le_self_pow_of_pos [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= a)
 (hn : 0 < n) : a <= a ^ n
参数：ha : 1 <= a；hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_self_pow₀`：le_self_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <
= a) (hn : n != 0) : a <= a ^ n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b

--- 原说明 ---
The `bound` tactic can't handle `m ≠ 0` goals yet, so we express as `0 < m`
-/
lemma Bound.le_self_pow_of_pos [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) (hn : 0 < n) :
    a ≤ a ^ n := le_self_pow₀ ha hn.ne'

@[mono, gcongr, bound]
/-
**pow_le_pow_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_le_pow_left₀ [PosMulMono M₀] [MulPosMono M₀]
    (ha : 0 ≤ a) (hab : a ≤ b) : ∀ n, a ^ n ≤ b ^ n
  | 0 => by simp
  | 1 => by simpa using hab
  | n + 2 => by simpa only [pow_succ']
      using mul_le_mul hab (pow_le_pow_left₀ ha hab _) (pow_succ_nonneg ha _) (ha.trans hab)
/-
**pow_left_monotoneOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_left_monotoneOn [PosMulMono M₀] [MulPosMono M₀] : MonotoneOn (fun a : 
M₀ => a ^ n) {x | 0 <= x}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
-/
lemma pow_left_monotoneOn [PosMulMono M₀] [MulPosMono M₀] :
    MonotoneOn (fun a : M₀ ↦ a ^ n) {x | 0 ≤ x} :=
  fun _a ha _b _ hab ↦ pow_le_pow_left₀ ha hab _

variable [Preorder α] {f g : α → M₀}
/-
**monotone_mul_left_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monotone_mul_left_of_nonneg [PosMulMono M₀] (ha : 0 <= a) : Monotone fun x
 => a * x
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
-/
lemma monotone_mul_left_of_nonneg [PosMulMono M₀] (ha : 0 ≤ a) : Monotone fun x ↦ a * x :=
  fun _ _ h ↦ mul_le_mul_of_nonneg_left h ha
/-
**monotone_mul_right_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monotone_mul_right_of_nonneg [MulPosMono M₀] (ha : 0 <= a) : Monotone fun 
x => x * a
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
-/
lemma monotone_mul_right_of_nonneg [MulPosMono M₀] (ha : 0 ≤ a) : Monotone fun x ↦ x * a :=
  fun _ _ h ↦ mul_le_mul_of_nonneg_right h ha
/-
**Monotone.mul_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.mul_const [MulPosMono M₀] (hf : Monotone f) (ha : 0 <= a) : Monot
one fun x => f x * a
参数：hf : Monotone f；ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用引理 `monotone_mul_right_of_nonneg`：monotone_mul_right_of_nonneg [MulPosMono M
₀] (ha : 0 <= a) : Monotone fun x => x * a
-/
lemma Monotone.mul_const [MulPosMono M₀] (hf : Monotone f) (ha : 0 ≤ a) :
    Monotone fun x ↦ f x * a := (monotone_mul_right_of_nonneg ha).comp hf
/-
**Monotone.const_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.const_mul [PosMulMono M₀] (hf : Monotone f) (ha : 0 <= a) : Monot
one fun x => a * f x
参数：hf : Monotone f；ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用引理 `monotone_mul_left_of_nonneg`：monotone_mul_left_of_nonneg [PosMulMono M₀]
 (ha : 0 <= a) : Monotone fun x => a * x
-/
lemma Monotone.const_mul [PosMulMono M₀] (hf : Monotone f) (ha : 0 ≤ a) :
    Monotone fun x ↦ a * f x := (monotone_mul_left_of_nonneg ha).comp hf
/-
**Antitone.mul_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Antitone.mul_const [MulPosMono M₀] (hf : Antitone f) (ha : 0 <= a) : Antit
one fun x => f x * a
参数：hf : Antitone f；ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp_antitone`：Monotone.comp_antitone (hg : Monotone g) (hf : A
ntitone f) : Antitone (g ∘ f)
· 使用引理 `monotone_mul_right_of_nonneg`：monotone_mul_right_of_nonneg [MulPosMono M
₀] (ha : 0 <= a) : Monotone fun x => x * a
-/
lemma Antitone.mul_const [MulPosMono M₀] (hf : Antitone f) (ha : 0 ≤ a) :
    Antitone fun x ↦ f x * a := (monotone_mul_right_of_nonneg ha).comp_antitone hf
/-
**Antitone.const_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Antitone.const_mul [PosMulMono M₀] (hf : Antitone f) (ha : 0 <= a) : Antit
one fun x => a * f x
参数：hf : Antitone f；ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp_antitone`：Monotone.comp_antitone (hg : Monotone g) (hf : A
ntitone f) : Antitone (g ∘ f)
· 使用引理 `monotone_mul_left_of_nonneg`：monotone_mul_left_of_nonneg [PosMulMono M₀]
 (ha : 0 <= a) : Monotone fun x => a * x
-/
lemma Antitone.const_mul [PosMulMono M₀] (hf : Antitone f) (ha : 0 ≤ a) :
    Antitone fun x ↦ a * f x := (monotone_mul_left_of_nonneg ha).comp_antitone hf

end Preorder

section PartialOrder
variable [PartialOrder M₀] {a b c d : M₀} {m n : ℕ}

/-
**mul_self_lt_mul_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_self_lt_mul_self [PosMulStrictMono M₀] [MulPosMono M₀] (ha : 0 <= a) (
hab : a < b) : a * a < b * b
参数：ha : 0 <= a；hab : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul'`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 :
 Preorder α] {a b c d : α} [PosMulStrictMono α]   [MulPosMono α], a ≤ b → c < d 
→…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
lemma mul_self_lt_mul_self [PosMulStrictMono M₀] [MulPosMono M₀] (ha : 0 ≤ a) (hab : a < b) :
    a * a < b * b := mul_lt_mul' hab.le hab ha <| ha.trans_lt hab

-- In the next lemma, we used to write `Set.Ici 0` instead of `{x | 0 ≤ x}`.
-- As this lemma is not used outside this file,
-- and the import for `Set.Ici` is not otherwise needed until later,
-- we choose not to use it here.
/-
**strictMonoOn_mul_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictMonoOn_mul_self [PosMulStrictMono M₀] [MulPosMono M₀] : StrictMonoOn
 (fun x => x * x) {x : M₀ | 0 <= x}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mul_self_lt_mul_self`：mul_self_lt_mul_self [PosMulStrictMono M₀] [MulPos
Mono M₀] (ha : 0 <= a) (hab : a < b) : a * a < b * b
-/
lemma strictMonoOn_mul_self [PosMulStrictMono M₀] [MulPosMono M₀] :
    StrictMonoOn (fun x ↦ x * x) {x : M₀ | 0 ≤ x} := fun _ hx _ _ hxy ↦ mul_self_lt_mul_self hx hxy

-- See Note [decidable namespace]
/-
**Decidable.mul_lt_mul''** 是 Mathlib 中的一个定理，位于命名空间 `Decidable`。
形式化陈述：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialOrder M₀] {a
 b c d : M₀} [PosMulMono M₀]   [PosMulStrictMono M₀] [MulPosStrictMono M₀] [Deci
dableLE M₀], a < c → b < d → 0 ≤ a → 0 ≤ b → a * b < c * d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.lt_or_eq_dec`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α} [
DecidableLE α], a ≤ b → a < b ∨ a = b
· 使用定理 `mul_lt_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α]   [MulPosStrictMono α], a < b → c ≤ d →
…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
protected lemma Decidable.mul_lt_mul'' [PosMulMono M₀] [PosMulStrictMono M₀] [MulPosStrictMono M₀]
    [DecidableLE M₀] (h1 : a < c) (h2 : b < d) (h3 : 0 ≤ a) (h4 : 0 ≤ b) : a * b < c * d :=
  h4.lt_or_eq_dec.elim (fun b0 ↦ mul_lt_mul h1 h2.le b0 <| h3.trans h1.le) fun b0 ↦ by
    rw [← b0, mul_zero]; exact mul_pos (h3.trans_lt h1) (h4.trans_lt h2)
/-
**lt_mul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_mul_left [MulPosStrictMono M₀] (ha : 0 < a) (hb : 1 < b) : a < b * a
参数：ha : 0 < a；hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
-/
lemma lt_mul_left [MulPosStrictMono M₀] (ha : 0 < a) (hb : 1 < b) : a < b * a := by
  simpa using mul_lt_mul_of_pos_right hb ha
/-
**lt_mul_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_mul_right [PosMulStrictMono M₀] (ha : 0 < a) (hb : 1 < b) : a < a * b
参数：ha : 0 < a；hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
-/
lemma lt_mul_right [PosMulStrictMono M₀] (ha : 0 < a) (hb : 1 < b) : a < a * b := by
  simpa using mul_lt_mul_of_pos_left hb ha
/-
**lt_mul_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_mul_self [ZeroLEOneClass M₀] [MulPosStrictMono M₀] (ha : 1 < a) : a < a
 * a
参数：ha : 1 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_mul_left`：lt_mul_left [MulPosStrictMono M₀] (ha : 0 < a) (hb : 1 < b)
 : a < b * a
· 使用定理 `LT.lt.trans_le'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a
 → c ≤ b → c < a
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
lemma lt_mul_self [ZeroLEOneClass M₀] [MulPosStrictMono M₀] (ha : 1 < a) : a < a * a :=
  lt_mul_left (ha.trans_le' zero_le_one) ha
/-
**sq_pos_of_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sq_pos_of_pos [PosMulStrictMono M₀] (ha : 0 < a) : 0 < a ^ 2
参数：ha : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
-/
lemma sq_pos_of_pos [PosMulStrictMono M₀] (ha : 0 < a) : 0 < a ^ 2 := by
  simpa only [sq] using mul_pos ha ha

section strict_mono
variable [PosMulStrictMono M₀]

/-
**pow_succ_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialOrder M₀] {a
 : M₀} [PosMulStrictMono M₀],   0 < a → ∀ (n : ℕ), 0 < a ^ (n + 1)
参数：n : ℕ；n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pow_succ_pos (ha : 0 < a) : ∀ n, 0 < a ^ (n + 1)
  | 0 => by simpa using ha
  | _ + 1 => pow_succ a _ ▸ mul_pos (pow_succ_pos ha _) ha
/-
**pow_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialOrder M₀] {a
 : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n : ℕ), 0 < a ^ n
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pow_pos [ZeroLEOneClass M₀] (ha : 0 < a) : ∀ n, 0 < a ^ n
  | 0 => by nontriviality; rw [pow_zero]; exact zero_lt_one
  | _ + 1 => pow_succ a _ ▸ mul_pos (pow_pos ha _) ha

@[gcongr, bound]
/-
**pow_lt_pow_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_lt_pow_left₀ [MulPosMono M₀] (hab : a < b)
    (ha : 0 ≤ a) : ∀ {n : ℕ}, n ≠ 0 → a ^ n < b ^ n
  | 1, _ => by simpa using hab
  | n + 2, _ => by
    simpa only [pow_succ] using mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
      (pow_le_pow_left₀ ha hab.le _) hab ha (pow_succ_pos (ha.trans_lt hab) _)

/-- See also `pow_left_strictMono₀` and `Nat.pow_left_strictMono`. -/
/-
**pow_left_strictMonoOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See also `pow_left_strictMono₀` and `Nat.pow_left_strictMono`.
-/
lemma pow_left_strictMonoOn₀ [MulPosMono M₀] (hn : n ≠ 0) :
    StrictMonoOn (· ^ n : M₀ → M₀) {a | 0 ≤ a} :=
  fun _a ha _b _ hab ↦ pow_lt_pow_left₀ hab ha hn

section ZeroLEOneClass

variable [ZeroLEOneClass M₀]

/-- See also `pow_right_strictMono'`. -/
/-
**pow_right_strictMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See also `pow_right_strictMono'`.
-/
lemma pow_right_strictMono₀ (h : 1 < a) : StrictMono (a ^ ·) :=
  strictMono_nat_of_lt_succ fun n => by
    simpa only [one_mul, pow_succ] using lt_mul_right (pow_pos (zero_le_one.trans_lt h) _) h

@[gcongr]
/-
**pow_lt_pow_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_lt_pow_right₀ (h : 1 < a) (hmn : m < n) : a ^ m < a ^ n := pow_right_strictMono₀ h hmn
/-
**pow_lt_pow_iff_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_lt_pow_iff_right₀ (h : 1 < a) : a ^ n < a ^ m ↔ n < m :=
  (pow_right_strictMono₀ h).lt_iff_lt
/-
**pow_le_pow_iff_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_le_pow_iff_right₀ (h : 1 < a) : a ^ n ≤ a ^ m ↔ n ≤ m :=
  (pow_right_strictMono₀ h).le_iff_le
/-
**lt_self_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lt_self_pow₀ (h : 1 < a) (hm : 1 < m) : a < a ^ m := by
  simpa only [pow_one] using pow_lt_pow_right₀ h hm

end ZeroLEOneClass

/-
**pow_right_strictAnti** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_right_strictAnti₀ (h₀ : 0 < a) (h₁ : a < 1) : StrictAnti (a ^ ·) :=
  strictAnti_nat_of_succ_lt fun n => by
    have : ZeroLEOneClass M₀ := ⟨(h₀.trans h₁).le⟩
    simpa only [pow_succ, mul_one] using mul_lt_mul_of_pos_left h₁ (pow_pos h₀ n)
/-
**pow_le_pow_iff_right_of_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_le_pow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : a ^ m ≤ a ^ n ↔ n ≤ m :=
  (pow_right_strictAnti₀ ha₀ ha₁).le_iff_ge
/-
**pow_lt_pow_iff_right_of_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_lt_pow_iff_right_of_lt_one₀ (h₀ : 0 < a) (h₁ : a < 1) : a ^ m < a ^ n ↔ n < m :=
  (pow_right_strictAnti₀ h₀ h₁).lt_iff_gt
/-
**pow_lt_pow_right_of_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_lt_pow_right_of_lt_one₀ (h₀ : 0 < a) (h₁ : a < 1) (hmn : m < n) : a ^ n < a ^ m :=
  (pow_lt_pow_iff_right_of_lt_one₀ h₀ h₁).2 hmn
/-
**pow_lt_self_of_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_lt_self_of_lt_one₀ (h₀ : 0 < a) (h₁ : a < 1) (hn : 1 < n) : a ^ n < a := by
  simpa only [pow_one] using pow_lt_pow_right_of_lt_one₀ h₀ h₁ hn

end strict_mono

variable [Preorder α] {f g : α → M₀}

/-
**strictMono_mul_left_of_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictMono_mul_left_of_pos [PosMulStrictMono M₀] (ha : 0 < a) : StrictMono
 fun x => a * x
参数：ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
-/
lemma strictMono_mul_left_of_pos [PosMulStrictMono M₀] (ha : 0 < a) :
    StrictMono fun x ↦ a * x := fun _ _ b_lt_c ↦ mul_lt_mul_of_pos_left b_lt_c ha
/-
**strictMono_mul_right_of_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictMono_mul_right_of_pos [MulPosStrictMono M₀] (ha : 0 < a) : StrictMon
o fun x => x * a
参数：ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
-/
lemma strictMono_mul_right_of_pos [MulPosStrictMono M₀] (ha : 0 < a) :
    StrictMono fun x ↦ x * a := fun _ _ b_lt_c ↦ mul_lt_mul_of_pos_right b_lt_c ha
/-
**StrictMono.mul_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.mul_const [MulPosStrictMono M₀] (hf : StrictMono f) (ha : 0 < a
) : StrictMono fun x => f x * a
参数：hf : StrictMono f；ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用引理 `strictMono_mul_right_of_pos`：strictMono_mul_right_of_pos [MulPosStrictMo
no M₀] (ha : 0 < a) : StrictMono fun x => x * a
-/
lemma StrictMono.mul_const [MulPosStrictMono M₀] (hf : StrictMono f) (ha : 0 < a) :
    StrictMono fun x ↦ f x * a := (strictMono_mul_right_of_pos ha).comp hf
/-
**StrictMono.const_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.const_mul [PosMulStrictMono M₀] (hf : StrictMono f) (ha : 0 < a
) : StrictMono fun x => a * f x
参数：hf : StrictMono f；ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用引理 `strictMono_mul_left_of_pos`：strictMono_mul_left_of_pos [PosMulStrictMono
 M₀] (ha : 0 < a) : StrictMono fun x => a * x
-/
lemma StrictMono.const_mul [PosMulStrictMono M₀] (hf : StrictMono f) (ha : 0 < a) :
    StrictMono fun x ↦ a * f x := (strictMono_mul_left_of_pos ha).comp hf
/-
**StrictAnti.mul_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAnti.mul_const [MulPosStrictMono M₀] (hf : StrictAnti f) (ha : 0 < a
) : StrictAnti fun x => f x * a
参数：hf : StrictAnti f；ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.comp_strictAnti`：StrictMono.comp_strictAnti (hg : StrictMono 
g) (hf : StrictAnti f) : StrictAnti (g ∘ f)
· 使用引理 `strictMono_mul_right_of_pos`：strictMono_mul_right_of_pos [MulPosStrictMo
no M₀] (ha : 0 < a) : StrictMono fun x => x * a
-/
lemma StrictAnti.mul_const [MulPosStrictMono M₀] (hf : StrictAnti f) (ha : 0 < a) :
    StrictAnti fun x ↦ f x * a := (strictMono_mul_right_of_pos ha).comp_strictAnti hf
/-
**StrictAnti.const_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictAnti.const_mul [PosMulStrictMono M₀] (hf : StrictAnti f) (ha : 0 < a
) : StrictAnti fun x => a * f x
参数：hf : StrictAnti f；ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.comp_strictAnti`：StrictMono.comp_strictAnti (hg : StrictMono 
g) (hf : StrictAnti f) : StrictAnti (g ∘ f)
· 使用引理 `strictMono_mul_left_of_pos`：strictMono_mul_left_of_pos [PosMulStrictMono
 M₀] (ha : 0 < a) : StrictMono fun x => a * x
-/
lemma StrictAnti.const_mul [PosMulStrictMono M₀] (hf : StrictAnti f) (ha : 0 < a) :
    StrictAnti fun x ↦ a * f x := (strictMono_mul_left_of_pos ha).comp_strictAnti hf
/-
**StrictMono.mul_monotone** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.mul_monotone [PosMulMono M₀] [MulPosStrictMono M₀] (hf : Strict
Mono f) (hg : Monotone g) (hf₀ : forall x, 0 <= f x) (hg₀ : forall x, 0 < g x) :
 StrictMono (f * g)
参数：hf : StrictMono f；hg : Monotone g；hf₀ : forall x, 0 <= f x；hg₀ : forall x, 0 
< g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α]   [MulPosStrictMono α], a < b → c ≤ d →
…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma StrictMono.mul_monotone [PosMulMono M₀] [MulPosStrictMono M₀] (hf : StrictMono f)
    (hg : Monotone g) (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 < g x) :
    StrictMono (f * g) := fun _ _ h ↦ mul_lt_mul (hf h) (hg h.le) (hg₀ _) (hf₀ _)
/-
**Monotone.mul_strictMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.mul_strictMono [PosMulStrictMono M₀] [MulPosMono M₀] (hf : Monoto
ne f) (hg : StrictMono g) (hf₀ : forall x, 0 < f x) (hg₀ : forall x, 0 <= g x) :
 StrictMono (f * g)
参数：hf : Monotone f；hg : StrictMono g；hf₀ : forall x, 0 < f x；hg₀ : forall x, 0 <
= g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul'`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 :
 Preorder α] {a b c d : α} [PosMulStrictMono α]   [MulPosMono α], a ≤ b → c < d 
→…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma Monotone.mul_strictMono [PosMulStrictMono M₀] [MulPosMono M₀] (hf : Monotone f)
    (hg : StrictMono g) (hf₀ : ∀ x, 0 < f x) (hg₀ : ∀ x, 0 ≤ g x) :
    StrictMono (f * g) := fun _ _ h ↦ mul_lt_mul' (hf h.le) (hg h) (hg₀ _) (hf₀ _)
/-
**StrictMono.mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.mul [PosMulStrictMono M₀] [MulPosStrictMono M₀] (hf : StrictMon
o f) (hg : StrictMono g) (hf₀ : forall x, 0 <= f x) (hg₀ : forall x, 0 <= g x) :
 StrictMono (f * g)
参数：hf : StrictMono f；hg : StrictMono g；hf₀ : forall x, 0 <= f x；hg₀ : forall x, 
0 <= g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul''`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b c d : α} [in
st_1 : Preorder α] [PosMulStrictMono α] [MulPosMono α],   a < b → c < d → 0 ≤ a 
→ …
· 使用定理 `MulPosStrictMono.toMulPosMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [MulPosStrictMono α], MulPosMono α
-/
lemma StrictMono.mul [PosMulStrictMono M₀] [MulPosStrictMono M₀] (hf : StrictMono f)
    (hg : StrictMono g) (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 ≤ g x) :
    StrictMono (f * g) := fun _ _ h ↦ mul_lt_mul'' (hf h) (hg h) (hf₀ _) (hg₀ _)

end PartialOrder

section LinearOrder
variable [LinearOrder M₀] [PosMulStrictMono M₀] {a b : M₀}
  {m n : ℕ}

/-
**pow_le_pow_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_le_pow_iff_left {a b : M} {n : Nat} (hn : n != 0) : a ^ n <= b ^ n ↔ a
 <= b
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `pow_left_strictMono`：pow_left_strictMono (hn : n != 0) : StrictMono (· ^
 n : M -> M)
-/
lemma pow_le_pow_iff_left₀ [MulPosMono M₀] (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) :
    a ^ n ≤ b ^ n ↔ a ≤ b :=
  (pow_left_strictMonoOn₀ hn).le_iff_le ha hb
/-
**pow_lt_pow_iff_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_lt_pow_iff_left₀ [MulPosMono M₀] (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) :
    a ^ n < b ^ n ↔ a < b :=
  (pow_left_strictMonoOn₀ hn).lt_iff_lt ha hb

@[simp]
/-
**pow_left_inj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_left_inj (hn : n != 0) : a ^ n = b ^ n ↔ a = b
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `pow_left_injective`：pow_left_injective (hn : n != 0) : Injective fun a :
 M => a ^ n
-/
lemma pow_left_inj₀ [MulPosMono M₀] (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) :
    a ^ n = b ^ n ↔ a = b :=
  (pow_left_strictMonoOn₀ hn).eq_iff_eq ha hb

section ZeroLEOneClass

variable [ZeroLEOneClass M₀]

/-
**pow_right_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_right_injective₀ (ha₀ : 0 < a) (ha₁ : a ≠ 1) : Injective (a ^ ·) := by
  obtain ha₁ | ha₁ := ha₁.lt_or_gt
  · exact (pow_right_strictAnti₀ ha₀ ha₁).injective
  · exact (pow_right_strictMono₀ ha₁).injective

@[simp]
/-
**pow_right_inj** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_right_inj₀ (ha₀ : 0 < a) (ha₁ : a ≠ 1) : a ^ m = a ^ n ↔ m = n :=
  (pow_right_injective₀ ha₀ ha₁).eq_iff
/-
**pow_le_one_iff_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_le_one_iff_of_nonneg (ha : 0 <= a) (hn : n != 0) : a ^ n <= 1 ↔ a <= 1
参数：ha : 0 <= a；hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `one_lt_pow₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preo
rder M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   1 < a → ∀ {n : ℕ}, n ≠ 
0…
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用引理 `pow_le_one₀`：pow_le_one₀ [PosMulMono M₀] {n : Nat} (ha₀ : 0 <= a) (ha₁ :
 a <= 1) : a ^ n <= 1
-/
lemma pow_le_one_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : a ^ n ≤ 1 ↔ a ≤ 1 := by
  refine ⟨fun h ↦ ?_, pow_le_one₀ ha⟩
  contrapose! h
  exact one_lt_pow₀ h hn
/-
**one_le_pow_iff_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_le_pow_iff_of_nonneg (ha : 0 <= a) (hn : n != 0) : 1 <= a ^ n ↔ 1 <= a
参数：ha : 0 <= a；hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `pow_lt_one₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preo
rder M₀] {a : M₀} [PosMulMono M₀],   0 ≤ a → a < 1 → ∀ {n : ℕ}, n ≠ 0 → a ^ n < 
1
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用引理 `one_le_pow₀`：one_le_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= 
a) {n : Nat} : 1 <= a ^ n
-/
lemma one_le_pow_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : 1 ≤ a ^ n ↔ 1 ≤ a := by
  refine ⟨fun h ↦ ?_, fun h ↦ one_le_pow₀ h⟩
  contrapose! h
  exact pow_lt_one₀ ha h hn
/-
**pow_lt_one_iff_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_lt_one_iff_of_nonneg (ha : 0 <= a) (hn : n != 0) : a ^ n < 1 ↔ a < 1
参数：ha : 0 <= a；hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用引理 `one_le_pow_iff_of_nonneg`：one_le_pow_iff_of_nonneg (ha : 0 <= a) (hn : n
 != 0) : 1 <= a ^ n ↔ 1 <= a
-/
lemma pow_lt_one_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : a ^ n < 1 ↔ a < 1 :=
  lt_iff_lt_of_le_iff_le (one_le_pow_iff_of_nonneg ha hn)
/-
**one_lt_pow_iff_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_lt_pow_iff_of_nonneg (ha : 0 <= a) (hn : n != 0) : 1 < a ^ n ↔ 1 < a
参数：ha : 0 <= a；hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_le_one_iff_of_nonneg`：pow_le_one_iff_of_nonneg (ha : 0 <= a) (hn : n
 != 0) : a ^ n <= 1 ↔ a <= 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma one_lt_pow_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : 1 < a ^ n ↔ 1 < a := by
  simp only [← not_le, pow_le_one_iff_of_nonneg ha hn]
/-
**pow_eq_one_iff_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_eq_one_iff_of_nonneg (ha : 0 <= a) (hn : n != 0) : a ^ n = 1 ↔ a = 1
参数：ha : 0 <= a；hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_le_one_iff_of_nonneg`：pow_le_one_iff_of_nonneg (ha : 0 <= a) (hn : n
 != 0) : a ^ n <= 1 ↔ a <= 1
· 使用引理 `one_le_pow_iff_of_nonneg`：one_le_pow_iff_of_nonneg (ha : 0 <= a) (hn : n
 != 0) : 1 <= a ^ n ↔ 1 <= a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma pow_eq_one_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : a ^ n = 1 ↔ a = 1 := by
  simp only [le_antisymm_iff, pow_le_one_iff_of_nonneg ha hn, one_le_pow_iff_of_nonneg ha hn]
/-
**sq_le_one_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sq_le_one_iff₀ (ha : 0 ≤ a) : a ^ 2 ≤ 1 ↔ a ≤ 1 :=
  pow_le_one_iff_of_nonneg ha (Nat.succ_ne_zero _)
/-
**sq_lt_one_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sq_lt_one_iff₀ (ha : 0 ≤ a) : a ^ 2 < 1 ↔ a < 1 :=
  pow_lt_one_iff_of_nonneg ha (Nat.succ_ne_zero _)
/-
**one_le_sq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_le_sq_iff₀ (ha : 0 ≤ a) : 1 ≤ a ^ 2 ↔ 1 ≤ a :=
  one_le_pow_iff_of_nonneg ha (Nat.succ_ne_zero _)
/-
**one_lt_sq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_lt_sq_iff₀ (ha : 0 ≤ a) : 1 < a ^ 2 ↔ 1 < a :=
  one_lt_pow_iff_of_nonneg ha (Nat.succ_ne_zero _)

end ZeroLEOneClass

variable [MulPosMono M₀]

/-
**lt_of_pow_lt_pow_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lt_of_pow_lt_pow_left₀ (n : ℕ) (hb : 0 ≤ b) (h : a ^ n < b ^ n) : a < b :=
  lt_of_not_ge fun hn => not_lt_of_ge (pow_le_pow_left₀ hb hn _) h
/-
**le_of_pow_le_pow_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le_of_pow_le_pow_left₀ (hn : n ≠ 0) (hb : 0 ≤ b) (h : a ^ n ≤ b ^ n) : a ≤ b :=
  le_of_not_gt fun h1 => not_le_of_gt (pow_lt_pow_left₀ h1 hb hn) h
/-
**sq_eq_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sq_eq_sq₀ (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 = b ^ 2 ↔ a = b := by
  simp [ha, hb]
/-
**lt_of_mul_self_lt_mul_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lt_of_mul_self_lt_mul_self₀ (hb : 0 ≤ b) : a * a < b * b → a < b := by
  simp only [← sq]
  exact lt_of_pow_lt_pow_left₀ _ hb
/-
**sq_lt_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sq_lt_sq : a ^ 2 < b ^ 2 ↔ |a| < |b|
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用引理 `sq_lt_sq₀`：sq_lt_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 < b ^ 2 ↔ a < b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
lemma sq_lt_sq₀ (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 < b ^ 2 ↔ a < b :=
  pow_lt_pow_iff_left₀ ha hb two_ne_zero
/-
**sq_le_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sq_le_sq : a ^ 2 <= b ^ 2 ↔ |a| <= |b|
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用引理 `sq_le_sq₀`：sq_le_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 <= b ^ 2 ↔ a <=
 b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
lemma sq_le_sq₀ (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 ≤ b ^ 2 ↔ a ≤ b :=
  pow_le_pow_iff_left₀ ha hb two_ne_zero

end MonoidWithZero.LinearOrder

section CancelMonoidWithZero

variable [MonoidWithZero α]

section PartialOrder

variable [PartialOrder α]

/-
**PosMulMono.toPosMulStrictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PosMulMono.toPosMulStrictMono [IsLeftCancelMulZero α] [PosMulMono α] : Pos
MulStrictMono α where mul_lt_mul_of_pos_left _a ha _b _c hbc
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem PosMulMono.toPosMulStrictMono [IsLeftCancelMulZero α] [PosMulMono α] :
    PosMulStrictMono α where
  mul_lt_mul_of_pos_left _a ha _b _c hbc :=
    (mul_le_mul_of_nonneg_left hbc.le ha.le).lt_of_ne (hbc.ne ∘ mul_left_cancel₀ ha.ne')
/-
**posMulMono_iff_posMulStrictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：posMulMono_iff_posMulStrictMono [IsLeftCancelMulZero α] : PosMulMono α ↔ P
osMulStrictMono α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosMulMono.toPosMulStrictMono`：PosMulMono.toPosMulStrictMono [IsLeftCanc
elMulZero α] [PosMulMono α] : PosMulStrictMono α where mul_lt_mul_of_pos_left _a
 ha _b _c hbc
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
-/
theorem posMulMono_iff_posMulStrictMono [IsLeftCancelMulZero α] :
    PosMulMono α ↔ PosMulStrictMono α :=
  ⟨(·.toPosMulStrictMono), (·.toPosMulMono)⟩
/-
**MulPosMono.toMulPosStrictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulPosMono.toMulPosStrictMono [IsRightCancelMulZero α] [MulPosMono α] : Mu
lPosStrictMono α where mul_lt_mul_of_pos_right _a ha _b _c hbc
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `mul_right_cancel₀`：mul_right_cancel₀ (hb : b != 0) (h : a * b = c * b) :
 a = c
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem MulPosMono.toMulPosStrictMono [IsRightCancelMulZero α] [MulPosMono α] :
    MulPosStrictMono α where
  mul_lt_mul_of_pos_right _a ha _b _c hbc :=
    (mul_le_mul_of_nonneg_right hbc.le ha.le).lt_of_ne (hbc.ne ∘ mul_right_cancel₀ ha.ne')
/-
**mulPosMono_iff_mulPosStrictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulPosMono_iff_mulPosStrictMono [IsRightCancelMulZero α] : MulPosMono α ↔ 
MulPosStrictMono α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulPosMono.toMulPosStrictMono`：MulPosMono.toMulPosStrictMono [IsRightCan
celMulZero α] [MulPosMono α] : MulPosStrictMono α where mul_lt_mul_of_pos_right 
_a ha _b _c hbc
· 使用定理 `MulPosStrictMono.toMulPosMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [MulPosStrictMono α], MulPosMono α
-/
theorem mulPosMono_iff_mulPosStrictMono [IsRightCancelMulZero α] :
    MulPosMono α ↔ MulPosStrictMono α :=
  ⟨(·.toMulPosStrictMono), (·.toMulPosMono)⟩
/-
**PosMulReflectLT.toPosMulReflectLE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PosMulReflectLT.toPosMulReflectLE [IsLeftCancelMulZero α] [PosMulReflectLT
 α] : PosMulReflectLE α where elim
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lt_of_mul_lt_mul_left`：lt_of_mul_lt_mul_left [PosMulReflectLT α] (h : a 
* b < a * c) (a0 : 0 <= a) : b < c
-/
theorem PosMulReflectLT.toPosMulReflectLE [IsLeftCancelMulZero α] [PosMulReflectLT α] :
    PosMulReflectLE α where
  elim := fun x _ _ h =>
    h.eq_or_lt.elim (le_of_eq ∘ mul_left_cancel₀ x.2.ne.symm) fun h' =>
      (lt_of_mul_lt_mul_left h' x.2.le).le
/-
**posMulReflectLE_iff_posMulReflectLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：posMulReflectLE_iff_posMulReflectLT [IsLeftCancelMulZero α] : PosMulReflec
tLE α ↔ PosMulReflectLT α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulReflectLT.toPosMulReflectLE`：PosMulReflectLT.toPosMulReflectLE [Is
LeftCancelMulZero α] [PosMulReflectLT α] : PosMulReflectLE α where elim
-/
theorem posMulReflectLE_iff_posMulReflectLT [IsLeftCancelMulZero α] :
    PosMulReflectLE α ↔ PosMulReflectLT α :=
  ⟨(·.toPosMulReflectLT), (·.toPosMulReflectLE)⟩
/-
**MulPosReflectLT.toMulPosReflectLE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulPosReflectLT.toMulPosReflectLE [IsRightCancelMulZero α] [MulPosReflectL
T α] : MulPosReflectLE α where elim
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `mul_right_cancel₀`：mul_right_cancel₀ (hb : b != 0) (h : a * b = c * b) :
 a = c
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lt_of_mul_lt_mul_right`：lt_of_mul_lt_mul_right [MulPosReflectLT α] (h : 
b * a < c * a) (a0 : 0 <= a) : b < c
-/
theorem MulPosReflectLT.toMulPosReflectLE [IsRightCancelMulZero α] [MulPosReflectLT α] :
    MulPosReflectLE α where
  elim := fun x _ _ h => h.eq_or_lt.elim (le_of_eq ∘ mul_right_cancel₀ x.2.ne.symm) fun h' =>
    (lt_of_mul_lt_mul_right h' x.2.le).le
/-
**mulPosReflectLE_iff_mulPosReflectLT** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulPosReflectLE_iff_mulPosReflectLT [IsRightCancelMulZero α] : MulPosRefle
ctLE α ↔ MulPosReflectLT α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosReflectLT.toMulPosReflectLE`：MulPosReflectLT.toMulPosReflectLE [Is
RightCancelMulZero α] [MulPosReflectLT α] : MulPosReflectLE α where elim
-/
theorem mulPosReflectLE_iff_mulPosReflectLT [IsRightCancelMulZero α] :
    MulPosReflectLE α ↔ MulPosReflectLT α :=
  ⟨(·.toMulPosReflectLT), (·.toMulPosReflectLE)⟩

end PartialOrder

end CancelMonoidWithZero

section GroupWithZero
variable [GroupWithZero G₀]

section Preorder
variable [Preorder G₀] {a b c : G₀}

/-- Equality holds when `a ≠ 0`. See `mul_inv_cancel_left`. -/
/-
**mul_inv_left_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_inv_left_le (hb : 0 <= b) : a * (a⁻¹ * b) <= b
参数：hb : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_cancel_left₀`：mul_inv_cancel_left₀ (h : a != 0) (b : G₀) : a * (
a⁻¹ * b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Equality holds when `a ≠ 0`. See `mul_inv_cancel_left`.
-/
lemma mul_inv_left_le (hb : 0 ≤ b) : a * (a⁻¹ * b) ≤ b := by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/-- Equality holds when `a ≠ 0`. See `mul_inv_cancel_left`. -/
/-
**le_mul_inv_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_mul_inv_left (hb : b <= 0) : b <= a * (a⁻¹ * b)
参数：hb : b <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_cancel_left₀`：mul_inv_cancel_left₀ (h : a != 0) (b : G₀) : a * (
a⁻¹ * b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Equality holds when `a ≠ 0`. See `mul_inv_cancel_left`.
-/
lemma le_mul_inv_left (hb : b ≤ 0) : b ≤ a * (a⁻¹ * b) := by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/-- Equality holds when `a ≠ 0`. See `inv_mul_cancel_left`. -/
/-
**inv_mul_left_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inv_mul_left_le (hb : 0 <= b) : a⁻¹ * (a * b) <= b
参数：hb : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Equality holds when `a ≠ 0`. See `inv_mul_cancel_left`.
-/
lemma inv_mul_left_le (hb : 0 ≤ b) : a⁻¹ * (a * b) ≤ b := by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/-- Equality holds when `a ≠ 0`. See `inv_mul_cancel_left`. -/
/-
**le_inv_mul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_inv_mul_left (hb : b <= 0) : b <= a⁻¹ * (a * b)
参数：hb : b <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Equality holds when `a ≠ 0`. See `inv_mul_cancel_left`.
-/
lemma le_inv_mul_left (hb : b ≤ 0) : b ≤ a⁻¹ * (a * b) := by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/-- Equality holds when `b ≠ 0`. See `mul_inv_cancel_right`. -/
/-
**mul_inv_right_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_inv_right_le (ha : 0 <= a) : a * b * b⁻¹ <= a
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_cancel_right₀`：mul_inv_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b * b⁻¹ = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Equality holds when `b ≠ 0`. See `mul_inv_cancel_right`.
-/
lemma mul_inv_right_le (ha : 0 ≤ a) : a * b * b⁻¹ ≤ a := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

/-- Equality holds when `b ≠ 0`. See `mul_inv_cancel_right`. -/
/-
**le_mul_inv_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_mul_inv_right (ha : a <= 0) : a <= a * b * b⁻¹
参数：ha : a <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_cancel_right₀`：mul_inv_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b * b⁻¹ = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Equality holds when `b ≠ 0`. See `mul_inv_cancel_right`.
-/
lemma le_mul_inv_right (ha : a ≤ 0) : a ≤ a * b * b⁻¹ := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

/-- Equality holds when `b ≠ 0`. See `inv_mul_cancel_right`. -/
/-
**inv_mul_right_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inv_mul_right_le (ha : 0 <= a) : a * b⁻¹ * b <= a
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_cancel_right₀`：inv_mul_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b⁻¹ * b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Equality holds when `b ≠ 0`. See `inv_mul_cancel_right`.
-/
lemma inv_mul_right_le (ha : 0 ≤ a) : a * b⁻¹ * b ≤ a := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

/-- Equality holds when `b ≠ 0`. See `inv_mul_cancel_right`. -/
/-
**le_inv_mul_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_inv_mul_right (ha : a <= 0) : a <= a * b⁻¹ * b
参数：ha : a <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_cancel_right₀`：inv_mul_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b⁻¹ * b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Equality holds when `b ≠ 0`. See `inv_mul_cancel_right`.
-/
lemma le_inv_mul_right (ha : a ≤ 0) : a ≤ a * b⁻¹ * b := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

/-- Equality holds when `c ≠ 0`. See `mul_div_mul_right`. -/
/-
**mul_div_mul_right_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_div_mul_right_le (h : 0 <= a / b) : a * c / (b * c) <= a / b
参数：h : 0 <= a / b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_div_mul_right`：mul_div_mul_right (a b : G₀) (hc : c != 0) : a * c / 
(b * c) = a / b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
Equality holds when `c ≠ 0`. See `mul_div_mul_right`.
-/
lemma mul_div_mul_right_le (h : 0 ≤ a / b) : a * c / (b * c) ≤ a / b := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_right _ _ hc]

/-- Equality holds when `c ≠ 0`. See `mul_div_mul_right`. -/
/-
**le_mul_div_mul_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_mul_div_mul_right (h : a / b <= 0) : a / b <= a * c / (b * c)
参数：h : a / b <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_div_mul_right`：mul_div_mul_right (a b : G₀) (hc : c != 0) : a * c / 
(b * c) = a / b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
Equality holds when `c ≠ 0`. See `mul_div_mul_right`.
-/
lemma le_mul_div_mul_right (h : a / b ≤ 0) : a / b ≤ a * c / (b * c) := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_right _ _ hc]

end Preorder

section Preorder
variable [Preorder G₀] [ZeroLEOneClass G₀] {a b c : G₀}

/-- See `div_self` for the version with equality when `a ≠ 0`. -/
/-
**div_self_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_self_le_one (a : G₀) : a / a <= 1
参数：a : G₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
See `div_self` for the version with equality when `a ≠ 0`.
-/
lemma div_self_le_one (a : G₀) : a / a ≤ 1 := by obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/-- Equality holds when `a ≠ 0`. See `mul_inv_cancel`. -/
/-
**mul_inv_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_inv_le_one : a * a⁻¹ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `div_self_le_one`：div_self_le_one (a : G₀) : a / a <= 1

--- 原说明 ---
Equality holds when `a ≠ 0`. See `mul_inv_cancel`.
-/
lemma mul_inv_le_one : a * a⁻¹ ≤ 1 := by simpa only [div_eq_mul_inv] using div_self_le_one a

/-- Equality holds when `a ≠ 0`. See `inv_mul_cancel`. -/
/-
**inv_mul_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inv_mul_le_one : a⁻¹ * a <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Equality holds when `a ≠ 0`. See `inv_mul_cancel`.
-/
lemma inv_mul_le_one : a⁻¹ * a ≤ 1 := by obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

end Preorder

section PartialOrder
variable [PartialOrder G₀]

section PosMulReflectLT

variable [PosMulReflectLT G₀] {a b c : G₀}

/-
**inv_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [Po
sMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_mul_lt_mul_left`：lt_of_mul_lt_mul_left [PosMulReflectLT α] (h : a 
* b < a * c) (a0 : 0 <= a) : b < c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
@[simp] lemma inv_pos : 0 < a⁻¹ ↔ 0 < a := by
  suffices ∀ a : G₀, 0 < a → 0 < a⁻¹ from ⟨fun h ↦ inv_inv a ▸ this _ h, this a⟩
  intro a ha
  apply lt_of_mul_lt_mul_left _ ha.le
  apply lt_of_mul_lt_mul_left _ ha.le
  simpa [ha.ne']

alias ⟨_, inv_pos_of_pos⟩ := inv_pos
/-
**inv_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [Po
sMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma inv_nonneg : 0 ≤ a⁻¹ ↔ 0 ≤ a := by simp only [le_iff_eq_or_lt, inv_pos, zero_eq_inv]

alias ⟨_, inv_nonneg_of_nonneg⟩ := inv_nonneg
/-
**one_div_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_div_pos : 0 < 1 / a ↔ 0 < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
-/
lemma one_div_pos : 0 < 1 / a ↔ 0 < a := one_div a ▸ inv_pos
/-
**one_div_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_div_nonneg : 0 <= 1 / a ↔ 0 <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
-/
lemma one_div_nonneg : 0 ≤ 1 / a ↔ 0 ≤ a := one_div a ▸ inv_nonneg

variable (G₀) in
/-- For a group with zero, `PosMulReflectLT G₀` implies `PosMulStrictMono G₀`. -/
/-
**PosMulReflectLT.toPosMulStrictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PosMulReflectLT.toPosMulStrictMono : PosMulStrictMono G₀ where mul_lt_mul_
of_pos_left a ha b c hbc
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_mul_lt_mul_left`：lt_of_mul_lt_mul_left [PosMulReflectLT α] (h : a 
* b < a * c) (a0 : 0 <= a) : b < c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹

--- 原说明 ---
For a group with zero, `PosMulReflectLT G₀` implies `PosMulStrictMono G₀`.
-/
theorem PosMulReflectLT.toPosMulStrictMono : PosMulStrictMono G₀ where
  mul_lt_mul_of_pos_left a ha b c hbc :=
    lt_of_mul_lt_mul_left (by simpa [ha.ne']) (inv_pos_of_pos ha).le

variable (G₀) in
/-- For a group with zero, `PosMulReflectLT G₀`
allows us to upgrade `MulPosMono G₀` to `MulPosReflectLE G₀`.
The other implication holds without the `PosMulReflectLT G₀` assumption,
see `MulPosReflectLT.toMulPosStrictMono` for a stronger version below.

This theorem shows that in the presence of the assumption `PosMulReflectLT G₀`,
it makes no sense to optimize between assumptions `MulPosMono G₀`, `MulPosStrictMono G₀`,
`MulPosReflectLT G₀`, and `MulPosReflectLE G₀`. -/
/-
**MulPosReflectLE.of_posMulReflectLT_of_mulPosMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulPosReflectLE.of_posMulReflectLT_of_mulPosMono [MulPosMono G₀] : MulPosR
eflectLE G₀ where elim
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_cancel_right₀`：mul_inv_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b * b⁻¹ = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
For a group with zero, `PosMulReflectLT G₀`
allows us to upgrade `MulPosMono G₀` to `MulPosReflectLE G₀`.
The other implication holds without the `PosMulReflectLT G₀` assumption,
see `MulPosReflectLT.toMulPosStrictMono` for a stronger version below.

This theorem shows that in the presence of the assumption `PosMulReflectLT G₀`,
it makes no sense to optimize between assumptions `MulPosMono G₀`, `MulPosStrict
Mono G₀`,
`MulPosReflectLT G₀`, and `MulPosReflectLE G₀`.
-/
theorem MulPosReflectLE.of_posMulReflectLT_of_mulPosMono [MulPosMono G₀] : MulPosReflectLE G₀ where
  elim := by
    rintro ⟨a, ha⟩ b c h
    simpa [ha.ne'] using mul_le_mul_of_nonneg_right h (inv_nonneg.2 ha.le)

attribute [local instance] PosMulReflectLT.toPosMulStrictMono PosMulReflectLT.toPosMulReflectLE
/-
**div_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
参数：ha : 0 < a；hb : 0 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `PosMulReflectLT.toPosMulStrictMono`：PosMulReflectLT.toPosMulStrictMono :
 PosMulStrictMono G₀ where mul_lt_mul_of_pos_left a ha b c hbc
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
-/
lemma div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [div_eq_mul_inv]; exact mul_pos ha (inv_pos.2 hb)
/-
**div_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
参数：ha : 0 <= a；hb : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用定理 `PosMulReflectLT.toPosMulStrictMono`：PosMulReflectLT.toPosMulStrictMono :
 PosMulStrictMono G₀ where mul_lt_mul_of_pos_left a ha b c hbc
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
-/
lemma div_nonneg (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by
  rw [div_eq_mul_inv]; exact mul_nonneg ha (inv_nonneg.2 hb)

/-- See `le_inv_mul_iff₀'` for a version with multiplication on the other side. -/
/-
**le_inv_mul_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `le_inv_mul_iff₀'` for a version with multiplication on the other side.
-/
lemma le_inv_mul_iff₀ (hc : 0 < c) : a ≤ c⁻¹ * b ↔ c * a ≤ b := by
  rw [← mul_le_mul_iff_of_pos_left hc, mul_inv_cancel_left₀ hc.ne']

/-- See `inv_mul_le_iff₀'` for a version with multiplication on the other side. -/
/-
**inv_mul_le_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `inv_mul_le_iff₀'` for a version with multiplication on the other side.
-/
lemma inv_mul_le_iff₀ (hc : 0 < c) : c⁻¹ * b ≤ a ↔ b ≤ c * a := by
  rw [← mul_le_mul_iff_of_pos_left hc, mul_inv_cancel_left₀ hc.ne']
/-
**one_le_inv_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_le_inv_mul₀ (ha : 0 < a) : 1 ≤ a⁻¹ * b ↔ a ≤ b := by rw [le_inv_mul_iff₀ ha, mul_one]
/-
**inv_mul_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inv_mul_le_one : a⁻¹ * a <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma inv_mul_le_one₀ (ha : 0 < a) : a⁻¹ * b ≤ 1 ↔ b ≤ a := by rw [inv_mul_le_iff₀ ha, mul_one]

/-- See `inv_le_iff_one_le_mul₀` for a version with multiplication on the other side. -/
/-
**inv_le_iff_one_le_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_le_iff_one_le_mul : a⁻¹ <= b ↔ 1 <= b * a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `mul_le_mul_iff_right`：mul_le_mul_iff_right [MulRightMono α] [MulRightRef
lectLE α] (a : α) {b c : α} : b * a <= c * a ↔ b <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
See `inv_le_iff_one_le_mul₀` for a version with multiplication on the other side
.
-/
lemma inv_le_iff_one_le_mul₀' (ha : 0 < a) : a⁻¹ ≤ b ↔ 1 ≤ a * b := by
  rw [← inv_mul_le_iff₀ ha, mul_one]
/-
**one_le_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_le_inv₀ (ha : 0 < a) : 1 ≤ a⁻¹ ↔ a ≤ 1 := by simpa using one_le_inv_mul₀ ha (b := 1)
/-
**inv_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_le_one₀ (ha : 0 < a) : a⁻¹ ≤ 1 ↔ 1 ≤ a := by simpa using inv_mul_le_one₀ ha (b := 1)

@[bound] alias ⟨_, Bound.one_le_inv₀⟩ := one_le_inv₀

/-- One direction of `le_inv_mul_iff₀` where `c` is allowed to be `0` (but `b` must be nonnegative).
-/
/-
**mul_le_of_le_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : Group α] [inst_1 : LE α] [MulLeftMono α] {a b c : α
}, b ≤ a⁻¹ * c → a * b ≤ c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_inv_mul_iff_mul_le`：le_inv_mul_iff_mul_le : b <= a⁻¹ * c ↔ a * b <= c

--- 原说明 ---
One direction of `le_inv_mul_iff₀` where `c` is allowed to be `0` (but `b` must 
be nonnegative).
-/
lemma mul_le_of_le_inv_mul₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c⁻¹ * b) : c * a ≤ b := by
  obtain rfl | hc := hc.eq_or_lt
  · simpa using hb
  · rwa [le_inv_mul_iff₀ hc] at h

/-- One direction of `inv_mul_le_iff₀` where `b` is allowed to be `0` (but `c` must be nonnegative).
-/
/-
**inv_mul_le_of_le_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : Group α] [inst_1 : LE α] [MulLeftMono α] {a b c : α
}, a ≤ b * c → b⁻¹ * a ≤ c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_mul_le_iff_le_mul`：inv_mul_le_iff_le_mul : b⁻¹ * a <= c ↔ a <= b * c

--- 原说明 ---
One direction of `inv_mul_le_iff₀` where `b` is allowed to be `0` (but `c` must 
be nonnegative).
-/
lemma inv_mul_le_of_le_mul₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b * c) : b⁻¹ * a ≤ c := by
  obtain rfl | hb := hb.eq_or_lt
  · simp [hc]
  · rwa [inv_mul_le_iff₀ hb]

/-- See `lt_inv_mul_iff₀'` for a version with multiplication on the other side. -/
/-
**lt_inv_mul_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `lt_inv_mul_iff₀'` for a version with multiplication on the other side.
-/
lemma lt_inv_mul_iff₀ (hc : 0 < c) : a < c⁻¹ * b ↔ c * a < b := by
  rw [← mul_lt_mul_iff_of_pos_left hc, mul_inv_cancel_left₀ hc.ne']

/-- See `inv_mul_lt_iff₀'` for a version with multiplication on the other side. -/
/-
**inv_mul_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `inv_mul_lt_iff₀'` for a version with multiplication on the other side.
-/
lemma inv_mul_lt_iff₀ (hc : 0 < c) : c⁻¹ * b < a ↔ b < c * a := by
  rw [← mul_lt_mul_iff_of_pos_left hc, mul_inv_cancel_left₀ hc.ne']

/-- See `inv_lt_iff_one_lt_mul₀` for a version with multiplication on the other side. -/
/-
**inv_lt_iff_one_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_lt_iff_one_lt_mul : a⁻¹ < b ↔ 1 < b * a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `mul_lt_mul_iff_right`：mul_lt_mul_iff_right [MulRightStrictMono α] [MulRi
ghtReflectLT α] (a : α) {b c : α} : b * a < c * a ↔ b < c
· 使用定理 `Group.covconv_swap`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N]
 [CovariantClass N N (Function.swap fun x1 x2 => x1 * x2) r],   ContravariantCla
ss N N (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
See `inv_lt_iff_one_lt_mul₀` for a version with multiplication on the other side
.
-/
lemma inv_lt_iff_one_lt_mul₀' (ha : 0 < a) : a⁻¹ < b ↔ 1 < a * b := by
  rw [← inv_mul_lt_iff₀ ha, mul_one]
/-
**one_lt_inv_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_lt_inv_mul₀ (ha : 0 < a) : 1 < a⁻¹ * b ↔ a < b := by rw [lt_inv_mul_iff₀ ha, mul_one]
/-
**inv_mul_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_mul_lt_one₀ (ha : 0 < a) : a⁻¹ * b < 1 ↔ b < a := by rw [inv_mul_lt_iff₀ ha, mul_one]
/-
**one_lt_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_lt_inv₀ (ha : 0 < a) : 1 < a⁻¹ ↔ a < 1 := by simpa using one_lt_inv_mul₀ ha (b := 1)
/-
**inv_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_lt_one₀ (ha : 0 < a) : a⁻¹ < 1 ↔ 1 < a := by simpa using inv_mul_lt_one₀ ha (b := 1)

section ZeroLEOneClass

variable [ZeroLEOneClass G₀]

@[bound]
/-
**inv_lt_one_of_one_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_lt_one_of_one_lt : 1 < a -> a⁻¹ < 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_lt_one_iff_one_lt`：∀ {α : Type u} [inst : Group α] [inst_1 : LT α] [
MulLeftStrictMono α] {a : α}, a⁻¹ < 1 ↔ 1 < a
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma inv_lt_one_of_one_lt₀ (ha : 1 < a) : a⁻¹ < 1 := (inv_lt_one₀ <| zero_lt_one.trans ha).2 ha
/-
**one_lt_inv_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_lt_inv_iff₀ : 1 < a⁻¹ ↔ 0 < a ∧ a < 1 where
  mp h := ⟨inv_pos.1 (zero_lt_one.trans h), inv_inv a ▸ (inv_lt_one₀ <| zero_lt_one.trans h).2 h⟩
  mpr h := (one_lt_inv₀ h.1).2 h.2

@[bound]
/-
**inv_le_one_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_le_one_of_one_le : 1 <= a -> a⁻¹ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_le_one'`：∀ {α : Type u} [inst : Group α] [inst_1 : LE α] [MulLeftMon
o α] {a : α}, a⁻¹ ≤ 1 ↔ 1 ≤ a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma inv_le_one_of_one_le₀ (ha : 1 ≤ a) : a⁻¹ ≤ 1 :=
  (inv_le_one₀ <| zero_lt_one.trans_le ha).2 ha
/-
**one_le_inv_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_le_inv_iff₀ : 1 ≤ a⁻¹ ↔ 0 < a ∧ a ≤ 1 where
  mp h := ⟨inv_pos.1 (zero_lt_one.trans_le h),
    inv_inv a ▸ (inv_le_one₀ <| zero_lt_one.trans_le h).2 h⟩
  mpr h := (one_le_inv₀ h.1).2 h.2

@[bound]
/-
**inv_mul_le_one_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_mul_le_one_of_le₀ (h : a ≤ b) (hb : 0 ≤ b) : b⁻¹ * a ≤ 1 :=
  inv_mul_le_of_le_mul₀ hb zero_le_one <| by rwa [mul_one]

section ZPow
variable {m n : ℤ}

/-
**zpow_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [Po
sMulReflectLT G₀] {a : G₀}   [ZeroLEOneClass G₀], 0 ≤ a → ∀ (n : ℤ), 0 ≤ a ^ n
参数：n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用定理 `PosMulReflectLT.toPosMulStrictMono`：PosMulReflectLT.toPosMulStrictMono :
 PosMulStrictMono G₀ where mul_lt_mul_of_pos_left a ha b c hbc
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
-/
lemma zpow_nonneg (ha : 0 ≤ a) : ∀ n : ℤ, 0 ≤ a ^ n
  | (n : ℕ) => by rw [zpow_natCast]; exact pow_nonneg ha _
  | -(n + 1 : ℕ) => by rw [zpow_neg, inv_nonneg, zpow_natCast]; exact pow_nonneg ha _
/-
**zpow_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [Po
sMulReflectLT G₀] {a : G₀}   [ZeroLEOneClass G₀], 0 < a → ∀ (n : ℤ), 0 < a ^ n
参数：n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `PosMulReflectLT.toPosMulStrictMono`：PosMulReflectLT.toPosMulStrictMono :
 PosMulStrictMono G₀ where mul_lt_mul_of_pos_left a ha b c hbc
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
-/
lemma zpow_pos (ha : 0 < a) : ∀ n : ℤ, 0 < a ^ n
  | (n : ℕ) => by rw [zpow_natCast]; exact pow_pos ha _
  | -(n + 1 : ℕ) => by rw [zpow_neg, inv_pos, zpow_natCast]; exact pow_pos ha _
/-
**zpow_right_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_right_mono (ha : 1 <= a) : Monotone fun n : Int => a ^ n
参数：ha : 1 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_int_of_le_succ`：monotone_int_of_le_succ {f : Int -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_add_one`：∀ {G : Type u_3} [inst : Group G] (a : G) (n : ℤ), a ^ (n 
+ 1) = a ^ n * a
· 使用定理 `le_mul_of_one_le_right'`：le_mul_of_one_le_right' [MulLeftMono α] {a b : 
α} (h : 1 <= b) : a <= a * b
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma zpow_right_mono₀ (ha : 1 ≤ a) : Monotone fun n : ℤ ↦ a ^ n := by
  refine monotone_int_of_le_succ fun n ↦ ?_
  rw [zpow_add_one₀ (zero_lt_one.trans_le ha).ne']
  exact le_mul_of_one_le_right (zpow_nonneg (zero_le_one.trans ha) _) ha
/-
**zpow_right_anti** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zpow_right_anti₀ (ha₀ : 0 < a) (ha₁ : a ≤ 1) : Antitone fun n : ℤ ↦ a ^ n := by
  refine antitone_int_of_succ_le fun n ↦ ?_
  rw [zpow_add_one₀ ha₀.ne']
  exact mul_le_of_le_one_right (zpow_nonneg ha₀.le _) ha₁
/-
**zpow_right_strictMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_right_strictMono (ha : 1 < a) : StrictMono fun n : Int => a ^ n
参数：ha : 1 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_int_of_lt_succ`：strictMono_int_of_lt_succ {f : Int -> α} (hf 
: forall n, f n < f (n + 1)) : StrictMono f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_add_one`：∀ {G : Type u_3} [inst : Group G] (a : G) (n : ℤ), a ^ (n 
+ 1) = a ^ n * a
· 使用定理 `lt_mul_of_one_lt_right'`：lt_mul_of_one_lt_right' [MulLeftStrictMono α] (
a : α) {b : α} (h : 1 < b) : a < a * b
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma zpow_right_strictMono₀ (ha : 1 < a) : StrictMono fun n : ℤ ↦ a ^ n := by
  refine strictMono_int_of_lt_succ fun n ↦ ?_
  rw [zpow_add_one₀ (zero_lt_one.trans ha).ne']
  exact lt_mul_of_one_lt_right (zpow_pos (zero_lt_one.trans ha) _) ha
/-
**zpow_right_strictAnti** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_right_strictAnti (ha : a < 1) : StrictAnti fun n : Int => a ^ n
参数：ha : a < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictAnti_int_of_succ_lt`：strictAnti_int_of_succ_lt {f : Int -> α} (hf 
: forall n, f (n + 1) < f n) : StrictAnti f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_add_one`：∀ {G : Type u_3} [inst : Group G] (a : G) (n : ℤ), a ^ (n 
+ 1) = a ^ n * a
· 使用定理 `mul_lt_of_lt_one_right'`：mul_lt_of_lt_one_right' [MulLeftStrictMono α] (
a : α) {b : α} (h : b < 1) : a * b < a
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma zpow_right_strictAnti₀ (ha₀ : 0 < a) (ha₁ : a < 1) : StrictAnti fun n : ℤ ↦ a ^ n := by
  refine strictAnti_int_of_succ_lt fun n ↦ ?_
  rw [zpow_add_one₀ ha₀.ne']
  exact mul_lt_of_lt_one_right (zpow_pos ha₀ _) ha₁

@[gcongr]
/-
**zpow_le_zpow_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_le_zpow_right (ha : 1 <= a) (h : m <= n) : a ^ m <= a ^ n
参数：ha : 1 <= a；h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `zpow_right_mono`：zpow_right_mono (ha : 1 <= a) : Monotone fun n : Int =>
 a ^ n
-/
lemma zpow_le_zpow_right₀ (ha : 1 ≤ a) (hmn : m ≤ n) : a ^ m ≤ a ^ n := zpow_right_mono₀ ha hmn
/-
**zpow_le_zpow_right_of_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zpow_le_zpow_right_of_le_one₀ (ha₀ : 0 < a) (ha₁ : a ≤ 1) (hmn : m ≤ n) : a ^ n ≤ a ^ m :=
  zpow_right_anti₀ ha₀ ha₁ hmn
/-
**one_le_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_le_zpow {x : G} (H : 1 <= x) {n : Int} (hn : 0 <= n) : 1 <= x ^ n
参数：H : 1 <= x；hn : 0 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `one_le_pow_of_one_le'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preo
rder M] [MulLeftMono M] {a : M}, 1 ≤ a → ∀ (n : ℕ), 1 ≤ a ^ n
-/
lemma one_le_zpow₀ (ha : 1 ≤ a) (hn : 0 ≤ n) : 1 ≤ a ^ n := by simpa using zpow_right_mono₀ ha hn
/-
**zpow_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zpow_le_one₀ (ha₀ : 0 < a) (ha₁ : a ≤ 1) (hn : 0 ≤ n) : a ^ n ≤ 1 := by
  simpa using zpow_right_anti₀ ha₀ ha₁ hn
/-
**zpow_le_one_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zpow_le_one_of_nonpos₀ (ha : 1 ≤ a) (hn : n ≤ 0) : a ^ n ≤ 1 := by
  simpa using zpow_right_mono₀ ha hn
/-
**one_le_zpow_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_le_zpow_of_nonpos₀ (ha₀ : 0 < a) (ha₁ : a ≤ 1) (hn : n ≤ 0) : 1 ≤ a ^ n := by
  simpa using zpow_right_anti₀ ha₀ ha₁ hn

@[gcongr]
/-
**zpow_lt_zpow_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_lt_zpow_right (ha : 1 < a) (h : m < n) : a ^ m < a ^ n
参数：ha : 1 < a；h : m < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `zpow_right_strictMono`：zpow_right_strictMono (ha : 1 < a) : StrictMono f
un n : Int => a ^ n
-/
lemma zpow_lt_zpow_right₀ (ha : 1 < a) (hmn : m < n) : a ^ m < a ^ n :=
  zpow_right_strictMono₀ ha hmn
/-
**zpow_lt_zpow_right_of_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zpow_lt_zpow_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) (hmn : m < n) : a ^ n < a ^ m :=
  zpow_right_strictAnti₀ ha₀ ha₁ hmn
/-
**one_lt_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_lt_zpow {x : G} (hx : 1 < x) {n : Int} (hn : 0 < n) : 1 < x ^ n
参数：hx : 1 < x；hn : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `Int.le_of_lt`：∀ {a b : ℤ}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `one_lt_pow'`：one_lt_pow' (ha : 1 < a) {k : Nat} (hk : k != 0) : 1 < a ^ 
k
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.natCast_pos`：∀ {n : ℕ}, 0 < ↑n ↔ 0 < n
-/
lemma one_lt_zpow₀ (ha : 1 < a) (hn : 0 < n) : 1 < a ^ n := by
  simpa using zpow_right_strictMono₀ ha hn
/-
**zpow_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zpow_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) (hn : 0 < n) : a ^ n < 1 := by
  simpa using zpow_right_strictAnti₀ ha₀ ha₁ hn
/-
**zpow_lt_one_of_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zpow_lt_one_of_neg₀ (ha : 1 < a) (hn : n < 0) : a ^ n < 1 := by
  simpa using zpow_right_strictMono₀ ha hn
/-
**one_lt_zpow_of_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_lt_zpow_of_neg₀ (ha₀ : 0 < a) (ha₁ : a < 1) (hn : n < 0) : 1 < a ^ n := by
  simpa using zpow_right_strictAnti₀ ha₀ ha₁ hn
/-
**zpow_le_zpow_iff_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_le_zpow_iff_right (ha : 1 < a) : a ^ m <= a ^ n ↔ m <= n
参数：ha : 1 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `zpow_right_strictMono`：zpow_right_strictMono (ha : 1 < a) : StrictMono f
un n : Int => a ^ n
-/
@[simp] lemma zpow_le_zpow_iff_right₀ (ha : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n :=
  (zpow_right_strictMono₀ ha).le_iff_le
/-
**zpow_lt_zpow_iff_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_lt_zpow_iff_right (ha : 1 < a) : a ^ m < a ^ n ↔ m < n
参数：ha : 1 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `zpow_right_strictMono`：zpow_right_strictMono (ha : 1 < a) : StrictMono f
un n : Int => a ^ n
-/
@[simp] lemma zpow_lt_zpow_iff_right₀ (ha : 1 < a) : a ^ m < a ^ n ↔ m < n :=
  (zpow_right_strictMono₀ ha).lt_iff_lt
/-
**zpow_le_zpow_iff_right_of_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zpow_le_zpow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) :
    a ^ m ≤ a ^ n ↔ n ≤ m := (zpow_right_strictAnti₀ ha₀ ha₁).le_iff_ge
/-
**zpow_lt_zpow_iff_right_of_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zpow_lt_zpow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) :
    a ^ m < a ^ n ↔ n < m := (zpow_right_strictAnti₀ ha₀ ha₁).lt_iff_gt
/-
**one_le_zpow_iff_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma one_le_zpow_iff_right₀ (ha : 1 < a) : 1 ≤ a ^ n ↔ 0 ≤ n := by
  simp [← zpow_le_zpow_iff_right₀ ha]
/-
**one_lt_zpow_iff_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma one_lt_zpow_iff_right₀ (ha : 1 < a) : 1 < a ^ n ↔ 0 < n := by
  simp [← zpow_lt_zpow_iff_right₀ ha]
/-
**one_le_zpow_iff_right_of_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma one_le_zpow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : 1 ≤ a ^ n ↔ n ≤ 0 := by
  simp [← zpow_le_zpow_iff_right_of_lt_one₀ ha₀ ha₁]
/-
**one_lt_zpow_iff_right_of_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma one_lt_zpow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : 1 < a ^ n ↔ n < 0 := by
  simp [← zpow_lt_zpow_iff_right_of_lt_one₀ ha₀ ha₁]
/-
**zpow_le_one_iff_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma zpow_le_one_iff_right₀ (ha : 1 < a) : a ^ n ≤ 1 ↔ n ≤ 0 := by
  simp [← zpow_le_zpow_iff_right₀ ha]
/-
**zpow_lt_one_iff_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma zpow_lt_one_iff_right₀ (ha : 1 < a) : a ^ n < 1 ↔ n < 0 := by
  simp [← zpow_lt_zpow_iff_right₀ ha]
/-
**zpow_le_one_iff_right_of_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma zpow_le_one_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : a ^ n ≤ 1 ↔ 0 ≤ n := by
  simp [← zpow_le_zpow_iff_right_of_lt_one₀ ha₀ ha₁]
/-
**zpow_lt_one_iff_right_of_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma zpow_lt_one_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : a ^ n < 1 ↔ 0 < n := by
  simp [← zpow_lt_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

end ZPow

end ZeroLEOneClass

section MulPosMono

variable [MulPosMono G₀] {n : ℤ}

/-
**zpow_left_monoOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zpow_left_monoOn₀ (hn : 0 ≤ n) : MonotoneOn (fun a : G₀ ↦ a ^ n) {a | 0 ≤ a} := by
  lift n to ℕ using hn; simpa using pow_left_monotoneOn
/-
**zpow_left_strictMonoOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zpow_left_strictMonoOn₀ (hn : 0 < n) : StrictMonoOn (fun a : G₀ ↦ a ^ n) {a | 0 ≤ a} := by
  lift n to ℕ using hn.le; simpa using pow_left_strictMonoOn₀ (by lia)
/-
**zpow_le_zpow_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_le_zpow_left (hn : 0 <= n) (h : a <= b) : a ^ n <= b ^ n
参数：hn : 0 <= n；h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `zpow_left_mono`：zpow_left_mono (hn : 0 <= n) : Monotone ((· ^ n) : α -> 
α)
-/
lemma zpow_le_zpow_left₀ (hn : 0 ≤ n) (ha : 0 ≤ a) (h : a ≤ b) : a ^ n ≤ b ^ n :=
  zpow_left_monoOn₀ (G₀ := G₀) hn ha (by grind) h
/-
**zpow_lt_zpow_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_lt_zpow_left (hn : 0 < n) (h : a < b) : a ^ n < b ^ n
参数：hn : 0 < n；h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `zpow_left_strictMono`：zpow_left_strictMono (hn : 0 < n) : StrictMono ((·
 ^ n) : α -> α)
-/
lemma zpow_lt_zpow_left₀ (hn : 0 < n) (ha : 0 ≤ a) (h : a < b) : a ^ n < b ^ n :=
  zpow_left_strictMonoOn₀ (G₀ := G₀) hn ha (by grind) h

end MulPosMono

end PosMulReflectLT

section MulPosReflectLT
variable [MulPosReflectLT G₀] {a b c : G₀}

namespace Right

/-
**Right.inv_pos** 是 Mathlib 中的一个引理，位于命名空间 `Right`。
形式化陈述：inv_pos : 0 < a⁻¹ ↔ 0 < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_mul_lt_mul_right`：lt_of_mul_lt_mul_right [MulPosReflectLT α] (h : 
b * a < c * a) (a0 : 0 <= a) : b < c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
lemma inv_pos : 0 < a⁻¹ ↔ 0 < a := by
  suffices ∀ a : G₀, 0 < a → 0 < a⁻¹ from ⟨fun h ↦ inv_inv a ▸ this _ h, this a⟩
  intro a ha
  apply lt_of_mul_lt_mul_right _ ha.le
  apply lt_of_mul_lt_mul_right _ ha.le
  simpa [ha.ne']

variable (G₀) in
/-- For a group with zero, `MulPosReflectLT G₀` implies `MulPosStrictMono G₀`. -/
/-
**Right._root_.MulPosReflectLT.toMulPosStrictMono** 是 Mathlib 中的一个定理，位于命名空间 `Rig
ht`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a group with zero, `MulPosReflectLT G₀` implies `MulPosStrictMono G₀`.
-/
theorem _root_.MulPosReflectLT.toMulPosStrictMono : MulPosStrictMono G₀ where
  mul_lt_mul_of_pos_right a ha b c hbc :=
    lt_of_mul_lt_mul_right (by simpa [ha.ne']) (inv_pos.2 ha).le
/-
**Right.inv_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Right`。
形式化陈述：inv_nonneg : 0 <= a⁻¹ ↔ 0 <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma inv_nonneg : 0 ≤ a⁻¹ ↔ 0 ≤ a := by simp only [le_iff_eq_or_lt, inv_pos, zero_eq_inv]

end Right

attribute [local instance] PosMulReflectLT.toPosMulStrictMono
  MulPosReflectLT.toMulPosStrictMono MulPosReflectLT.toMulPosReflectLE

/-
**div_nonpos_of_nonpos_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_nonpos_of_nonpos_of_nonneg (ha : a <= 0) (hb : 0 <= b) : a / b <= 0
参数：ha : a <= 0；hb : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_nonpos_of_nonpos_of_nonneg`：mul_nonpos_of_nonpos_of_nonneg [MulPosMo
no α] (ha : a <= 0) (hb : 0 <= b) : a * b <= 0
· 使用定理 `MulPosStrictMono.toMulPosMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [MulPosStrictMono α], MulPosMono α
· 使用定理 `MulPosReflectLT.toMulPosStrictMono`：∀ (G₀ : Type u_3) [inst : GroupWithZ
ero G₀] [inst_1 : PartialOrder G₀] [MulPosReflectLT G₀], MulPosStrictMono G₀
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Right.inv_nonneg`：inv_nonneg : 0 <= a⁻¹ ↔ 0 <= a
-/
lemma div_nonpos_of_nonpos_of_nonneg (ha : a ≤ 0) (hb : 0 ≤ b) : a / b ≤ 0 := by
  rw [div_eq_mul_inv]; exact mul_nonpos_of_nonpos_of_nonneg ha (Right.inv_nonneg.2 hb)

/-- See `le_mul_inv_iff₀'` for a version with multiplication on the other side. -/
/-
**le_mul_inv_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `le_mul_inv_iff₀'` for a version with multiplication on the other side.
-/
lemma le_mul_inv_iff₀ (hc : 0 < c) : a ≤ b * c⁻¹ ↔ a * c ≤ b := by
  rw [← mul_le_mul_iff_of_pos_right hc, inv_mul_cancel_right₀ hc.ne']

/-- See `mul_inv_le_iff₀'` for a version with multiplication on the other side. -/
/-
**mul_inv_le_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `mul_inv_le_iff₀'` for a version with multiplication on the other side.
-/
lemma mul_inv_le_iff₀ (hc : 0 < c) : b * c⁻¹ ≤ a ↔ b ≤ a * c := by
  rw [← mul_le_mul_iff_of_pos_right hc, inv_mul_cancel_right₀ hc.ne']

/-- See `lt_mul_inv_iff₀'` for a version with multiplication on the other side. -/
/-
**lt_mul_inv_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `lt_mul_inv_iff₀'` for a version with multiplication on the other side.
-/
lemma lt_mul_inv_iff₀ (hc : 0 < c) : a < b * c⁻¹ ↔ a * c < b := by
  rw [← mul_lt_mul_iff_of_pos_right hc, inv_mul_cancel_right₀ hc.ne']

/-- See `mul_inv_lt_iff₀'` for a version with multiplication on the other side. -/
/-
**mul_inv_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `mul_inv_lt_iff₀'` for a version with multiplication on the other side.
-/
lemma mul_inv_lt_iff₀ (hc : 0 < c) : b * c⁻¹ < a ↔ b < a * c := by
  rw [← mul_lt_mul_iff_of_pos_right hc, inv_mul_cancel_right₀ hc.ne']

/-- See `le_div_iff₀'` for a version with multiplication on the other side. -/
/-
**le_div_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `le_div_iff₀'` for a version with multiplication on the other side.
-/
lemma le_div_iff₀ (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := by
  rw [div_eq_mul_inv, le_mul_inv_iff₀ hc]

/-- See `div_le_iff₀'` for a version with multiplication on the other side. -/
/-
**div_le_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `div_le_iff₀'` for a version with multiplication on the other side.
-/
lemma div_le_iff₀ (hc : 0 < c) : b / c ≤ a ↔ b ≤ a * c := by
  rw [div_eq_mul_inv, mul_inv_le_iff₀ hc]

/-- See `lt_div_iff₀'` for a version with multiplication on the other side. -/
/-
**lt_div_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `lt_div_iff₀'` for a version with multiplication on the other side.
-/
lemma lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b := by
  rw [div_eq_mul_inv, lt_mul_inv_iff₀ hc]

/-- See `div_lt_iff₀'` for a version with multiplication on the other side. -/
/-
**div_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `div_lt_iff₀'` for a version with multiplication on the other side.
-/
lemma div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c := by
  rw [div_eq_mul_inv, mul_inv_lt_iff₀ hc]
/-
**div_le_div_iff_of_pos_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_le_div_iff_of_pos_right (hc : 0 < c) : a / c <= b / c ↔ a <= b
参数：hc : 0 < c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma div_le_div_iff_of_pos_right (hc : 0 < c) : a / c ≤ b / c ↔ a ≤ b := by
  rw [div_le_iff₀ hc, div_mul_cancel₀ _ hc.ne']
/-
**div_lt_div_iff_of_pos_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_lt_div_iff_of_pos_right (hc : 0 < c) : a / c < b / c ↔ a < b
参数：hc : 0 < c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `div_lt_iff₀`：div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma div_lt_div_iff_of_pos_right (hc : 0 < c) : a / c < b / c ↔ a < b := by
  rw [div_lt_iff₀ hc, div_mul_cancel₀ _ hc.ne']

/-- See `inv_le_iff_one_le_mul₀'` for a version with multiplication on the other side. -/
/-
**inv_le_iff_one_le_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_le_iff_one_le_mul : a⁻¹ <= b ↔ 1 <= b * a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `mul_le_mul_iff_right`：mul_le_mul_iff_right [MulRightMono α] [MulRightRef
lectLE α] (a : α) {b c : α} : b * a <= c * a ↔ b <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
See `inv_le_iff_one_le_mul₀'` for a version with multiplication on the other sid
e.
-/
lemma inv_le_iff_one_le_mul₀ (ha : 0 < a) : a⁻¹ ≤ b ↔ 1 ≤ b * a := by
  rw [← mul_inv_le_iff₀ ha, one_mul]

/-- See `inv_lt_iff_one_lt_mul₀'` for a version with multiplication on the other side. -/
/-
**inv_lt_iff_one_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_lt_iff_one_lt_mul : a⁻¹ < b ↔ 1 < b * a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `mul_lt_mul_iff_right`：mul_lt_mul_iff_right [MulRightStrictMono α] [MulRi
ghtReflectLT α] (a : α) {b c : α} : b * a < c * a ↔ b < c
· 使用定理 `Group.covconv_swap`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N]
 [CovariantClass N N (Function.swap fun x1 x2 => x1 * x2) r],   ContravariantCla
ss N N (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
See `inv_lt_iff_one_lt_mul₀'` for a version with multiplication on the other sid
e.
-/
lemma inv_lt_iff_one_lt_mul₀ (ha : 0 < a) : a⁻¹ < b ↔ 1 < b * a := by
  rw [← mul_inv_lt_iff₀ ha, one_mul]
/-
**one_le_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_le_div (hb : 0 < b) : 1 <= a / b ↔ b <= a
参数：hb : 0 < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `PosMulReflectLT.toMulPosReflectLT`：PosMulReflectLT.toMulPosReflectLT [Po
sMulReflectLT α] : MulPosReflectLT α
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma one_le_div₀ (hb : 0 < b) : 1 ≤ a / b ↔ b ≤ a := by rw [le_div_iff₀ hb, one_mul]
/-
**one_lt_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_lt_div (hb : 0 < b) : 1 < a / b ↔ b < a
参数：hb : 0 < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `lt_div_iff₀`：lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b
· 使用定理 `PosMulReflectLT.toMulPosReflectLT`：PosMulReflectLT.toMulPosReflectLT [Po
sMulReflectLT α] : MulPosReflectLT α
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma one_lt_div₀ (hb : 0 < b) : 1 < a / b ↔ b < a := by rw [lt_div_iff₀ hb, one_mul]
/-
**div_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_le_one (hb : 0 < b) : a / b <= 1 ↔ a <= b
参数：hb : 0 < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `PosMulReflectLT.toMulPosReflectLT`：PosMulReflectLT.toMulPosReflectLT [Po
sMulReflectLT α] : MulPosReflectLT α
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma div_le_one₀ (hb : 0 < b) : a / b ≤ 1 ↔ a ≤ b := by rw [div_le_iff₀ hb, one_mul]
/-
**div_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b
参数：hb : 0 < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `div_lt_iff₀`：div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c
· 使用定理 `PosMulReflectLT.toMulPosReflectLT`：PosMulReflectLT.toMulPosReflectLT [Po
sMulReflectLT α] : MulPosReflectLT α
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma div_lt_one₀ (hb : 0 < b) : a / b < 1 ↔ a < b := by rw [div_lt_iff₀ hb, one_mul]

/-- One direction of `le_mul_inv_iff₀` where `c` is allowed to be `0` (but `b` must be nonnegative).
-/
/-
**mul_le_of_le_mul_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One direction of `le_mul_inv_iff₀` where `c` is allowed to be `0` (but `b` must 
be nonnegative).
-/
lemma mul_le_of_le_mul_inv₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b * c⁻¹) : a * c ≤ b := by
  obtain rfl | hc := hc.eq_or_lt
  · simpa using hb
  · rwa [le_mul_inv_iff₀ hc] at h

/-- One direction of `mul_inv_le_iff₀` where `b` is allowed to be `0` (but `c` must be nonnegative).
-/
/-
**mul_inv_le_of_le_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One direction of `mul_inv_le_iff₀` where `b` is allowed to be `0` (but `c` must 
be nonnegative).
-/
lemma mul_inv_le_of_le_mul₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c * b) : a * b⁻¹ ≤ c := by
  obtain rfl | hb := hb.eq_or_lt
  · simp [hc]
  · rwa [mul_inv_le_iff₀ hb]

/-- One direction of `le_div_iff₀` where `c` is allowed to be `0` (but `b` must be nonnegative). -/
/-
**mul_le_of_le_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One direction of `le_div_iff₀` where `c` is allowed to be `0` (but `b` must be n
onnegative).
-/
lemma mul_le_of_le_div₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b / c) : a * c ≤ b :=
  mul_le_of_le_mul_inv₀ hb hc (div_eq_mul_inv b _ ▸ h)

/-- One direction of `div_le_iff₀` where `b` is allowed to be `0` (but `c` must be nonnegative). -/
/-
**div_le_of_le_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One direction of `div_le_iff₀` where `b` is allowed to be `0` (but `c` must be n
onnegative).
-/
lemma div_le_of_le_mul₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c * b) : a / b ≤ c :=
  div_eq_mul_inv a _ ▸ mul_inv_le_of_le_mul₀ hb hc h

@[bound]
/-
**mul_inv_le_one_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_inv_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a ≤ b) (hb : 0 ≤ b) : a * b⁻¹ ≤ 1 :=
  mul_inv_le_of_le_mul₀ hb zero_le_one <| by rwa [one_mul]

@[bound]
/-
**div_le_one_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a ≤ b) (hb : 0 ≤ b) : a / b ≤ 1 :=
  div_le_of_le_mul₀ hb zero_le_one <| by rwa [one_mul]

@[mono, gcongr, bound]
/-
**div_le_div_of_nonneg_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_le_div_of_nonneg_right (hab : a <= b) (hc : 0 <= c) : a / c <= b / c
参数：hab : a <= b；hc : 0 <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `MulPosStrictMono.toMulPosMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [MulPosStrictMono α], MulPosMono α
· 使用定理 `MulPosReflectLT.toMulPosStrictMono`：∀ (G₀ : Type u_3) [inst : GroupWithZ
ero G₀] [inst_1 : PartialOrder G₀] [MulPosReflectLT G₀], MulPosStrictMono G₀
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Right.inv_nonneg`：inv_nonneg : 0 <= a⁻¹ ↔ 0 <= a
-/
lemma div_le_div_of_nonneg_right (hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c := by
  rw [div_eq_mul_inv a c, div_eq_mul_inv b c]
  gcongr; exact Right.inv_nonneg.2 hc

@[gcongr, bound]
/-
**div_lt_div_of_pos_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_lt_div_of_pos_right (h : a < b) (hc : 0 < c) : a / c < b / c
参数：h : a < b；hc : 0 < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `MulPosReflectLT.toMulPosStrictMono`：∀ (G₀ : Type u_3) [inst : GroupWithZ
ero G₀] [inst_1 : PartialOrder G₀] [MulPosReflectLT G₀], MulPosStrictMono G₀
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Right.inv_pos`：inv_pos : 0 < a⁻¹ ↔ 0 < a
-/
lemma div_lt_div_of_pos_right (h : a < b) (hc : 0 < c) : a / c < b / c := by
  rw [div_eq_mul_inv a c, div_eq_mul_inv b c]
  exact mul_lt_mul_of_pos_right h (Right.inv_pos.2 hc)

end MulPosReflectLT

section Both

variable [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b c d : G₀}

attribute [local instance] PosMulReflectLT.toPosMulStrictMono PosMulReflectLT.toPosMulReflectLE
  MulPosReflectLT.toMulPosStrictMono MulPosReflectLT.toMulPosReflectLE

/-- See `inv_anti₀` for the implication from right-to-left with one fewer assumption. -/
/-
**inv_le_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `inv_anti₀` for the implication from right-to-left with one fewer assumption
.
-/
lemma inv_le_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a := by
  rw [inv_le_iff_one_le_mul₀' ha, le_mul_inv_iff₀ hb, one_mul]

/-- See `inv_strictAnti₀` for the implication from right-to-left with one fewer assumption. -/
/-
**inv_lt_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `inv_strictAnti₀` for the implication from right-to-left with one fewer assu
mption.
-/
lemma inv_lt_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a := by
  rw [inv_lt_iff_one_lt_mul₀' ha, lt_mul_inv_iff₀ hb, one_mul]

@[gcongr, bound]
/-
**inv_anti** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_anti₀ (hb : 0 < b) (hba : b ≤ a) : a⁻¹ ≤ b⁻¹ := (inv_le_inv₀ (hb.trans_le hba) hb).2 hba

@[gcongr, bound]
/-
**inv_strictAnti** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_strictAnti₀ (hb : 0 < b) (hba : b < a) : a⁻¹ < b⁻¹ :=
  (inv_lt_inv₀ (hb.trans hba) hb).2 hba
/-
**strictAntiOn_inv_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictAntiOn_inv_pos : StrictAntiOn (fun x : G₀ => x⁻¹) {r | 0 < r}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `inv_strictAnti₀`：inv_strictAnti₀ (hb : 0 < b) (hba : b < a) : a⁻¹ < b⁻¹
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
-/
lemma strictAntiOn_inv_pos : StrictAntiOn (fun x : G₀ ↦ x⁻¹) {r | 0 < r} :=
  fun ⦃_⦄ ha ⦃_⦄ _ h ↦ inv_strictAnti₀ (Set.mem_ofPred.mp ha) h
/-
**antitoneOn_inv_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antitoneOn_inv_pos : AntitoneOn (fun x : G₀ => x⁻¹) {r | 0 < r}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAntiOn.antitoneOn`：∀ {α : Type u} {β : Type v} [inst : PartialOrde
r α] [inst_1 : Preorder β] {f : α → β} {s : Set α},   StrictAntiOn f s → Antiton
eOn f s
· 使用引理 `strictAntiOn_inv_pos`：strictAntiOn_inv_pos : StrictAntiOn (fun x : G₀ =>
 x⁻¹) {r | 0 < r}
-/
lemma antitoneOn_inv_pos : AntitoneOn (fun x : G₀ ↦ x⁻¹) {r | 0 < r} :=
  strictAntiOn_inv_pos.antitoneOn

/-- See also `inv_le_of_inv_le₀` for a one-sided implication with one fewer assumption. -/
/-
**inv_le_comm** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See also `inv_le_of_inv_le₀` for a one-sided implication with one fewer assumpti
on.
-/
lemma inv_le_comm₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b ↔ b⁻¹ ≤ a := by
  rw [← inv_le_inv₀ hb (inv_pos.2 ha), inv_inv]

/-- See also `inv_lt_of_inv_lt₀` for a one-sided implication with one fewer assumption. -/
/-
**inv_lt_comm** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See also `inv_lt_of_inv_lt₀` for a one-sided implication with one fewer assumpti
on.
-/
lemma inv_lt_comm₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b ↔ b⁻¹ < a := by
  rw [← inv_lt_inv₀ hb (inv_pos.2 ha), inv_inv]
/-
**inv_le_of_inv_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_le_of_inv_le₀ (ha : 0 < a) (h : a⁻¹ ≤ b) : b⁻¹ ≤ a :=
  (inv_le_comm₀ ha <| (inv_pos.2 ha).trans_le h).1 h
/-
**inv_lt_of_inv_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_lt_of_inv_lt₀ (ha : 0 < a) (h : a⁻¹ < b) : b⁻¹ < a :=
  (inv_lt_comm₀ ha <| (inv_pos.2 ha).trans h).1 h

/-- See also `le_inv_of_le_inv₀` for a one-sided implication with one fewer assumption. -/
/-
**le_inv_comm** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See also `le_inv_of_le_inv₀` for a one-sided implication with one fewer assumpti
on.
-/
lemma le_inv_comm₀ (ha : 0 < a) (hb : 0 < b) : a ≤ b⁻¹ ↔ b ≤ a⁻¹ := by
  rw [← inv_le_inv₀ (inv_pos.2 hb) ha, inv_inv]

/-- See also `lt_inv_of_lt_inv₀` for a one-sided implication with one fewer assumption. -/
/-
**lt_inv_comm** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See also `lt_inv_of_lt_inv₀` for a one-sided implication with one fewer assumpti
on.
-/
lemma lt_inv_comm₀ (ha : 0 < a) (hb : 0 < b) : a < b⁻¹ ↔ b < a⁻¹ := by
  rw [← inv_lt_inv₀ (inv_pos.2 hb) ha, inv_inv]
/-
**le_inv_of_le_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : Group α] [inst_1 : LE α] [MulLeftMono α] [MulRightM
ono α] {a b : α}, a ≤ b⁻¹ → b ≤ a⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_inv'`：le_inv' : a <= b⁻¹ ↔ b <= a⁻¹
-/
lemma le_inv_of_le_inv₀ (ha : 0 < a) (h : a ≤ b⁻¹) : b ≤ a⁻¹ :=
  (le_inv_comm₀ ha <| inv_pos.1 <| ha.trans_le h).1 h
/-
**lt_inv_of_lt_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : Group α] [inst_1 : LT α] [MulLeftStrictMono α] {a b
 : α} [MulRightStrictMono α],   a < b⁻¹ → b < a⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_inv'`：lt_inv' : a < b⁻¹ ↔ b < a⁻¹
-/
lemma lt_inv_of_lt_inv₀ (ha : 0 < a) (h : a < b⁻¹) : b < a⁻¹ :=
  (lt_inv_comm₀ ha <| inv_pos.1 <| ha.trans h).1 h
/-
**div_le_div_iff_of_pos_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_le_div_iff_of_pos_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b 
<= a / c ↔ c <= b
参数：ha : 0 < a；hb : 0 < b；hc : 0 < c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_le_mul_iff_right₀`：mul_le_mul_iff_right₀ [PosMulMono α] [PosMulRefle
ctLE α] (a0 : 0 < a) : a * b <= a * c ↔ b <= c
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用定理 `PosMulReflectLT.toPosMulStrictMono`：PosMulReflectLT.toPosMulStrictMono :
 PosMulStrictMono G₀ where mul_lt_mul_of_pos_left a ha b c hbc
· 使用定理 `PosMulReflectLT.toPosMulReflectLE`：PosMulReflectLT.toPosMulReflectLE [Is
LeftCancelMulZero α] [PosMulReflectLT α] : PosMulReflectLE α where elim
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用引理 `inv_le_inv₀`：inv_le_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ <= b⁻¹ ↔ b <= a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma div_le_div_iff_of_pos_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / b ≤ a / c ↔ c ≤ b := by
  simp only [div_eq_mul_inv, mul_le_mul_iff_right₀ ha, inv_le_inv₀ hb hc]
/-
**div_lt_div_iff_of_pos_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_lt_div_iff_of_pos_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b 
< a / c ↔ c < b
参数：ha : 0 < a；hb : 0 < b；hc : 0 < c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le'`：lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preor
der β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) (H' : b <= a ↔ d <= c) : b < a 
↔ d < c
· 使用引理 `div_le_div_iff_of_pos_left`：div_le_div_iff_of_pos_left (ha : 0 < a) (hb 
: 0 < b) (hc : 0 < c) : a / b <= a / c ↔ c <= b
-/
lemma div_lt_div_iff_of_pos_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b < a / c ↔ c < b :=
  lt_iff_lt_of_le_iff_le' (div_le_div_iff_of_pos_left ha hc hb)
    (div_le_div_iff_of_pos_left ha hb hc)

-- Not a `mono` lemma b/c `div_le_div₀` is strictly more general
/-
**div_le_div_of_nonneg_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_le_div_of_nonneg_left (ha : 0 <= a) (hc : 0 < c) (h : c <= b) : a / b 
<= a / c
参数：ha : 0 <= a；hc : 0 < c；h : c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用定理 `PosMulReflectLT.toPosMulStrictMono`：PosMulReflectLT.toPosMulStrictMono :
 PosMulStrictMono G₀ where mul_lt_mul_of_pos_left a ha b c hbc
· 使用引理 `inv_anti₀`：inv_anti₀ (hb : 0 < b) (hba : b <= a) : a⁻¹ <= b⁻¹
-/
lemma div_le_div_of_nonneg_left (ha : 0 ≤ a) (hc : 0 < c) (h : c ≤ b) : a / b ≤ a / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  gcongr
  exacts [ha, hc]

@[gcongr, bound]
/-
**div_lt_div_of_pos_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_lt_div_of_pos_left (ha : 0 < a) (hc : 0 < c) (h : c < b) : a / b < a /
 c
参数：ha : 0 < a；hc : 0 < c；h : c < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `div_lt_div_iff_of_pos_left`：div_lt_div_iff_of_pos_left (ha : 0 < a) (hb 
: 0 < b) (hc : 0 < c) : a / b < a / c ↔ c < b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
-/
lemma div_lt_div_of_pos_left (ha : 0 < a) (hc : 0 < c) (h : c < b) : a / b < a / c :=
  (div_lt_div_iff_of_pos_left ha (hc.trans h) hc).mpr h

@[mono, gcongr, bound]
/-
**div_le_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma div_le_div₀ (hc : 0 ≤ c) (hac : a ≤ c) (hd : 0 < d) (hdb : d ≤ b) : a / b ≤ c / d := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  gcongr
  exacts [inv_nonneg.2 <| hd.le.trans hdb, hc, hd]

@[gcongr]
/-
**div_lt_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma div_lt_div₀ (hac : a < c) (hdb : d ≤ b) (hc : 0 ≤ c) (hd : 0 < d) : a / b < c / d := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  apply mul_lt_mul hac (by gcongr; assumption) _ hc
  exact inv_pos.2 (hd.trans_le hdb)
/-
**div_lt_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma div_lt_div₀' (hac : a ≤ c) (hdb : d < b) (hc : 0 < c) (hd : 0 < d) : a / b < c / d := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_lt_mul' hac ((inv_lt_inv₀ (hd.trans hdb) hd).2 hdb)
    (inv_nonneg.2 <| hd.le.trans hdb.le) hc

end Both

end PartialOrder

section LinearOrder
variable [LinearOrder G₀] {a b c d : G₀}

section PosMulMono
variable [PosMulMono G₀]

/-
**inv_neg''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : LinearOrder G₀] {a :
 G₀} [PosMulMono G₀], a⁻¹ < 0 ↔ a < 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosMulMono.toPosMulReflectLT`：PosMulMono.toPosMulReflectLT [PosMulMono α
] : PosMulReflectLT α where elim
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma inv_neg'' : a⁻¹ < 0 ↔ a < 0 := by
  have := PosMulMono.toPosMulReflectLT (α := G₀); simp only [← not_le, inv_nonneg]
/-
**inv_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : LinearOrder G₀] {a :
 G₀} [PosMulMono G₀], a⁻¹ ≤ 0 ↔ a ≤ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosMulMono.toPosMulReflectLT`：PosMulMono.toPosMulReflectLT [PosMulMono α
] : PosMulReflectLT α where elim
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma inv_nonpos : a⁻¹ ≤ 0 ↔ a ≤ 0 := by
  have := PosMulMono.toPosMulReflectLT (α := G₀); simp only [← not_lt, inv_pos]

alias inv_lt_zero := inv_neg''
/-
**one_div_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_div_neg : 1 / a < 0 ↔ a < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_neg''`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : LinearO
rder G₀] {a : G₀} [PosMulMono G₀], a⁻¹ < 0 ↔ a < 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
-/
lemma one_div_neg : 1 / a < 0 ↔ a < 0 := one_div a ▸ inv_neg''
/-
**one_div_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_div_nonpos : 1 / a <= 0 ↔ a <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_nonpos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Linear
Order G₀] {a : G₀} [PosMulMono G₀], a⁻¹ ≤ 0 ↔ a ≤ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
-/
lemma one_div_nonpos : 1 / a ≤ 0 ↔ a ≤ 0 := one_div a ▸ inv_nonpos
/-
**div_nonpos_of_nonneg_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：div_nonpos_of_nonneg_of_nonpos (ha : 0 <= a) (hb : b <= 0) : a / b <= 0
参数：ha : 0 <= a；hb : b <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_nonpos_of_nonneg_of_nonpos`：mul_nonpos_of_nonneg_of_nonpos [PosMulMo
no α] (ha : 0 <= a) (hb : b <= 0) : a * b <= 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_nonpos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Linear
Order G₀] {a : G₀} [PosMulMono G₀], a⁻¹ ≤ 0 ↔ a ≤ 0
-/
lemma div_nonpos_of_nonneg_of_nonpos (ha : 0 ≤ a) (hb : b ≤ 0) : a / b ≤ 0 := by
  rw [div_eq_mul_inv]; exact mul_nonpos_of_nonneg_of_nonpos ha (inv_nonpos.2 hb)
/-
**neg_of_div_neg_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_of_div_neg_right (h : a / b < 0) (ha : 0 <= a) : b < 0
参数：h : a / b < 0；ha : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosMulMono.toPosMulReflectLT`：PosMulMono.toPosMulReflectLT [PosMulMono α
] : PosMulReflectLT α where elim
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
-/
lemma neg_of_div_neg_right (h : a / b < 0) (ha : 0 ≤ a) : b < 0 :=
  have := PosMulMono.toPosMulReflectLT (α := G₀)
  lt_of_not_ge fun hb ↦ (div_nonneg ha hb).not_gt h
/-
**neg_of_div_neg_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_of_div_neg_left (h : a / b < 0) (hb : 0 <= b) : a < 0
参数：h : a / b < 0；hb : 0 <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PosMulMono.toPosMulReflectLT`：PosMulMono.toPosMulReflectLT [PosMulMono α
] : PosMulReflectLT α where elim
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
-/
lemma neg_of_div_neg_left (h : a / b < 0) (hb : 0 ≤ b) : a < 0 :=
  have := PosMulMono.toPosMulReflectLT (α := G₀)
  lt_of_not_ge fun ha ↦ (div_nonneg ha hb).not_gt h

end PosMulMono

variable {m n : ℤ}

section ZeroLEOne

variable [PosMulStrictMono G₀]

variable [ZeroLEOneClass G₀]

/-
**inv_lt_one_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_lt_one_iff₀ : a⁻¹ < 1 ↔ a ≤ 0 ∨ 1 < a := by
  simp_rw [← not_le, one_le_inv_iff₀, not_and_or, not_lt]
/-
**inv_le_one_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_le_one_iff₀ : a⁻¹ ≤ 1 ↔ a ≤ 0 ∨ 1 ≤ a := by
  simp only [← not_lt, one_lt_inv_iff₀, not_and_or]
/-
**zpow_right_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zpow_right_injective₀ (ha₀ : 0 < a) (ha₁ : a ≠ 1) : Injective fun n : ℤ ↦ a ^ n := by
  obtain ha₁ | ha₁ := ha₁.lt_or_gt
  · exact (zpow_right_strictAnti₀ ha₀ ha₁).injective
  · exact (zpow_right_strictMono₀ ha₁).injective
/-
**zpow_right_inj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_right_inj (ha : 1 < a) {m n : Int} : a ^ m = a ^ n ↔ m = n
参数：ha : 1 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `zpow_right_strictMono`：zpow_right_strictMono (ha : 1 < a) : StrictMono f
un n : Int => a ^ n
-/
@[simp] lemma zpow_right_inj₀ (ha₀ : 0 < a) (ha₁ : a ≠ 1) : a ^ m = a ^ n ↔ m = n :=
  (zpow_right_injective₀ ha₀ ha₁).eq_iff
/-
**zpow_eq_one_iff_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zpow_eq_one_iff_right₀ (ha₀ : 0 ≤ a) (ha₁ : a ≠ 1) {n : ℤ} : a ^ n = 1 ↔ n = 0 := by
  obtain rfl | ha₀ := ha₀.eq_or_lt
  · exact zero_zpow_eq_one₀
  simpa using zpow_right_inj₀ ha₀ ha₁ (n := 0)

end ZeroLEOne

section MulPosMono

variable [PosMulReflectLT G₀] [MulPosMono G₀]

/-
**zpow_le_zpow_iff_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_le_zpow_iff_left (hn : 0 < n) : a ^ n <= b ^ n ↔ a <= b
参数：hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `zpow_left_strictMono`：zpow_left_strictMono (hn : 0 < n) : StrictMono ((·
 ^ n) : α -> α)
-/
lemma zpow_le_zpow_iff_left₀ (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : 0 < n) : a ^ n ≤ b ^ n ↔ a ≤ b :=
  (zpow_left_strictMonoOn₀ (G₀ := G₀) hn).le_iff_le ha hb
/-
**zpow_lt_zpow_iff_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_lt_zpow_iff_left (hn : 0 < n) : a ^ n < b ^ n ↔ a < b
参数：hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `zpow_left_strictMono`：zpow_left_strictMono (hn : 0 < n) : StrictMono ((·
 ^ n) : α -> α)
-/
lemma zpow_lt_zpow_iff_left₀ (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : 0 < n) : a ^ n < b ^ n ↔ a < b :=
  (zpow_left_strictMonoOn₀ (G₀ := G₀) hn).lt_iff_lt ha hb

end MulPosMono

section PosMulStrictMono
variable [PosMulStrictMono G₀] [MulPosMono G₀]

/-
**zpow_left_injOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zpow_left_injOn₀ : ∀ {n : ℤ}, n ≠ 0 → {a | 0 ≤ a}.InjOn fun a : G₀ ↦ a ^ n
  | (n + 1 : ℕ), _ => by simpa using! mod_cast (pow_left_strictMonoOn₀ n.succ_ne_zero).injOn
  | .negSucc n, _ => by
    simpa using! inv_injective.comp_injOn (pow_left_strictMonoOn₀ n.succ_ne_zero).injOn
/-
**zpow_left_inj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zpow_left_inj (hn : n != 0) : a ^ n = b ^ n ↔ a = b
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `zpow_left_injective`：∀ {G : Type u_2} [inst : Group G] [IsMulTorsionFree
 G] {n : ℤ}, n ≠ 0 → Function.Injective fun a => a ^ n
-/
lemma zpow_left_inj₀ (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) :
    a ^ n = b ^ n ↔ a = b := (zpow_left_injOn₀ hn).eq_iff ha hb

end PosMulStrictMono
end GroupWithZero.LinearOrder

section CommGroupWithZero

section Preorder
variable [CommGroupWithZero G₀] [Preorder G₀] {a b c : G₀}

/-- Equality holds when `c ≠ 0`. See `mul_div_mul_left`. -/
/-
**mul_div_mul_left_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_div_mul_left_le (h : 0 <= a / b) : c * a / (c * b) <= a / b
参数：h : 0 <= a / b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_div_mul_left`：mul_div_mul_left (a b : G₀) (hc : c != 0) : c * a / (c
 * b) = a / b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
Equality holds when `c ≠ 0`. See `mul_div_mul_left`.
-/
lemma mul_div_mul_left_le (h : 0 ≤ a / b) : c * a / (c * b) ≤ a / b := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_left _ _ hc]

/-- Equality holds when `c ≠ 0`. See `mul_div_mul_left`. -/
/-
**le_mul_div_mul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_mul_div_mul_left (h : a / b <= 0) : a / b <= c * a / (c * b)
参数：h : a / b <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_div_mul_left`：mul_div_mul_left (a b : G₀) (hc : c != 0) : c * a / (c
 * b) = a / b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
Equality holds when `c ≠ 0`. See `mul_div_mul_left`.
-/
lemma le_mul_div_mul_left (h : a / b ≤ 0) : a / b ≤ c * a / (c * b) := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_left _ _ hc]

end Preorder

variable [CommGroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c d : G₀}

attribute [local instance] PosMulReflectLT.toPosMulStrictMono PosMulMono.toMulPosMono
  PosMulStrictMono.toMulPosStrictMono PosMulReflectLT.toMulPosReflectLT

/-- See `le_inv_mul_iff₀` for a version with multiplication on the other side. -/
/-
**le_inv_mul_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `le_inv_mul_iff₀` for a version with multiplication on the other side.
-/
lemma le_inv_mul_iff₀' (hc : 0 < c) : a ≤ c⁻¹ * b ↔ a * c ≤ b := by
  rw [le_inv_mul_iff₀ hc, mul_comm]

/-- See `inv_mul_le_iff₀` for a version with multiplication on the other side. -/
/-
**inv_mul_le_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `inv_mul_le_iff₀` for a version with multiplication on the other side.
-/
lemma inv_mul_le_iff₀' (hc : 0 < c) : c⁻¹ * b ≤ a ↔ b ≤ a * c := by
  rw [inv_mul_le_iff₀ hc, mul_comm]

/-- See `le_mul_inv_iff₀` for a version with multiplication on the other side. -/
/-
**le_mul_inv_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `le_mul_inv_iff₀` for a version with multiplication on the other side.
-/
lemma le_mul_inv_iff₀' (hc : 0 < c) : a ≤ b * c⁻¹ ↔ c * a ≤ b := by
  rw [le_mul_inv_iff₀ hc, mul_comm]

/-- See `mul_inv_le_iff₀` for a version with multiplication on the other side. -/
/-
**mul_inv_le_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `mul_inv_le_iff₀` for a version with multiplication on the other side.
-/
lemma mul_inv_le_iff₀' (hc : 0 < c) : b * c⁻¹ ≤ a ↔ b ≤ c * a := by
  rw [mul_inv_le_iff₀ hc, mul_comm]
/-
**div_le_div_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma div_le_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a / b ≤ c / d ↔ a * d ≤ c * b := by
  rw [div_le_iff₀ hb, ← mul_div_right_comm, le_div_iff₀ hd]

/-- See `le_div_iff₀` for a version with multiplication on the other side. -/
/-
**le_div_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `le_div_iff₀` for a version with multiplication on the other side.
-/
lemma le_div_iff₀' (hc : 0 < c) : a ≤ b / c ↔ c * a ≤ b := by
  rw [le_div_iff₀ hc, mul_comm]

/-- See `div_le_iff₀` for a version with multiplication on the other side. -/
/-
**div_le_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `div_le_iff₀` for a version with multiplication on the other side.
-/
lemma div_le_iff₀' (hc : 0 < c) : b / c ≤ a ↔ b ≤ c * a := by
  rw [div_le_iff₀ hc, mul_comm]
/-
**le_div_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_div_comm : a <= b / c ↔ c <= b / a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `le_div_iff_mul_le'`：le_div_iff_mul_le' : b <= c / a ↔ a * b <= c
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `le_div_iff_mul_le`：le_div_iff_mul_le : a <= c / b ↔ a * b <= c
-/
lemma le_div_comm₀ (ha : 0 < a) (hc : 0 < c) : a ≤ b / c ↔ c ≤ b / a := by
  rw [le_div_iff₀ ha, le_div_iff₀' hc]
/-
**div_le_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_le_comm : a / b <= c ↔ a / c <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `div_le_iff_le_mul'`：div_le_iff_le_mul' : a / b <= c ↔ a <= b * c
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `div_le_iff_le_mul`：div_le_iff_le_mul : a / c <= b ↔ a <= b * c
-/
lemma div_le_comm₀ (hb : 0 < b) (hc : 0 < c) : a / b ≤ c ↔ a / c ≤ b := by
  rw [div_le_iff₀ hb, div_le_iff₀' hc]

/-- See `lt_inv_mul_iff₀` for a version with multiplication on the other side. -/
/-
**lt_inv_mul_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `lt_inv_mul_iff₀` for a version with multiplication on the other side.
-/
lemma lt_inv_mul_iff₀' (hc : 0 < c) : a < c⁻¹ * b ↔ a * c < b := by
  rw [lt_inv_mul_iff₀ hc, mul_comm]

/-- See `inv_mul_lt_iff₀` for a version with multiplication on the other side. -/
/-
**inv_mul_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `inv_mul_lt_iff₀` for a version with multiplication on the other side.
-/
lemma inv_mul_lt_iff₀' (hc : 0 < c) : c⁻¹ * b < a ↔ b < a * c := by
  rw [inv_mul_lt_iff₀ hc, mul_comm]

/-- See `lt_mul_inv_iff₀` for a version with multiplication on the other side. -/
/-
**lt_mul_inv_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `lt_mul_inv_iff₀` for a version with multiplication on the other side.
-/
lemma lt_mul_inv_iff₀' (hc : 0 < c) : a < b * c⁻¹ ↔ c * a < b := by
  rw [lt_mul_inv_iff₀ hc, mul_comm]

/-- See `mul_inv_lt_iff₀` for a version with multiplication on the other side. -/
/-
**mul_inv_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `mul_inv_lt_iff₀` for a version with multiplication on the other side.
-/
lemma mul_inv_lt_iff₀' (hc : 0 < c) : b * c⁻¹ < a ↔ b < c * a := by
  rw [mul_inv_lt_iff₀ hc, mul_comm]
/-
**div_lt_div_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma div_lt_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a / b < c / d ↔ a * d < c * b := by
  rw [div_lt_iff₀ hb, ← mul_div_right_comm, lt_div_iff₀ hd]

/-- See `lt_div_iff₀` for a version with multiplication on the other side. -/
/-
**lt_div_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `lt_div_iff₀` for a version with multiplication on the other side.
-/
lemma lt_div_iff₀' (hc : 0 < c) : a < b / c ↔ c * a < b := by
  rw [lt_div_iff₀ hc, mul_comm]

/-- See `div_lt_iff₀` for a version with multiplication on the other side. -/
/-
**div_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `div_lt_iff₀` for a version with multiplication on the other side.
-/
lemma div_lt_iff₀' (hc : 0 < c) : b / c < a ↔ b < c * a := by
  rw [div_lt_iff₀ hc, mul_comm]
/-
**lt_div_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_div_comm : a < b / c ↔ c < b / a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `lt_div_iff_mul_lt'`：lt_div_iff_mul_lt' : b < c / a ↔ a * b < c
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `lt_div_iff_mul_lt`：lt_div_iff_mul_lt : a < c / b ↔ a * b < c
-/
lemma lt_div_comm₀ (ha : 0 < a) (hc : 0 < c) : a < b / c ↔ c < b / a := by
  rw [lt_div_iff₀ ha, lt_div_iff₀' hc]
/-
**div_lt_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_lt_comm : a / b < c ↔ a / c < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `div_lt_iff_lt_mul'`：div_lt_iff_lt_mul' : a / b < c ↔ a < b * c
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `div_lt_iff_lt_mul`：div_lt_iff_lt_mul : a / c < b ↔ a < b * c
-/
lemma div_lt_comm₀ (hb : 0 < b) (hc : 0 < c) : a / b < c ↔ a / c < b := by
  rw [div_lt_iff₀ hb, div_lt_iff₀' hc]

end CommGroupWithZero

