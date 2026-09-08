/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Logic.Basic
public import Mathlib.Order.Defs.PartialOrder

/-!
# `NeZero` typeclass

We give basic facts about the `NeZero n` typeclass.

-/

public section

variable {R : Type*} [Zero R]

/-
**not_neZero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_neZero {n : R} : ¬NeZero n ↔ n = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_neZero {n : R} : ¬NeZero n ↔ n = 0 := by simp [neZero_iff]
/-
**eq_zero_or_neZero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
-/
theorem eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a :=
  (eq_or_ne a 0).imp_right NeZero.mk

section
variable {α : Type*} [Zero α]

/-
**zero_ne_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1], 0 ≠ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.ne'`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], 0 ≠
 n
-/
@[simp] lemma zero_ne_one [One α] [NeZero (1 : α)] : (0 : α) ≠ 1 := NeZero.ne' (1 : α)
/-
**one_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1], 1 ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
@[simp] lemma one_ne_zero [One α] [NeZero (1 : α)] : (1 : α) ≠ 0 := NeZero.ne (1 : α)
/-
**ne_zero_of_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ne_zero_of_eq_one [One α] [NeZero (1 : α)] {a : α} (h : a = 1) : a != 0
参数：1 : α；h : a = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ne_zero_of_eq_one [One α] [NeZero (1 : α)] {a : α} (h : a = 1) : a ≠ 0 := h ▸ one_ne_zero
/-
**two_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
参数：2 : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
lemma two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) ≠ 0 := NeZero.ne (2 : α)
/-
**three_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：three_ne_zero [OfNat α 3] [NeZero (3 : α)] : (3 : α) != 0
参数：3 : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
lemma three_ne_zero [OfNat α 3] [NeZero (3 : α)] : (3 : α) ≠ 0 := NeZero.ne (3 : α)
/-
**four_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：four_ne_zero [OfNat α 4] [NeZero (4 : α)] : (4 : α) != 0
参数：4 : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
lemma four_ne_zero [OfNat α 4] [NeZero (4 : α)] : (4 : α) ≠ 0 := NeZero.ne (4 : α)

variable (α)
/-
**zero_ne_one'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：zero_ne_one' [One α] [NeZero (1 : α)] : (0 : α) != 1
参数：1 : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
-/
lemma zero_ne_one' [One α] [NeZero (1 : α)] : (0 : α) ≠ 1 := zero_ne_one
/-
**one_ne_zero'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) != 0
参数：1 : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
lemma one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) ≠ 0 := one_ne_zero
/-
**two_ne_zero'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
参数：2 : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
-/
lemma two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) ≠ 0 := two_ne_zero
/-
**three_ne_zero'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：three_ne_zero' [OfNat α 3] [NeZero (3 : α)] : (3 : α) != 0
参数：3 : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `three_ne_zero`：three_ne_zero [OfNat α 3] [NeZero (3 : α)] : (3 : α) != 0
-/
lemma three_ne_zero' [OfNat α 3] [NeZero (3 : α)] : (3 : α) ≠ 0 := three_ne_zero
/-
**four_ne_zero'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：four_ne_zero' [OfNat α 4] [NeZero (4 : α)] : (4 : α) != 0
参数：4 : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `four_ne_zero`：four_ne_zero [OfNat α 4] [NeZero (4 : α)] : (4 : α) != 0
-/
lemma four_ne_zero' [OfNat α 4] [NeZero (4 : α)] : (4 : α) ≠ 0 := four_ne_zero

end

namespace NeZero

variable {M : Type*} {x : M}

/-
**NeZero.of_pos** 是 Mathlib 中的一个定理，位于命名空间 `NeZero`。
形式化陈述：of_pos [Preorder M] [Zero M] (h : 0 < x) : NeZero x
参数：h : 0 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem of_pos [Preorder M] [Zero M] (h : 0 < x) : NeZero x := ⟨ne_of_gt h⟩

end NeZero

