/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Yaël Dillies
-/
module

public import Mathlib.Order.Cover
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Preorder.Finite

/-!
# Intervals as finsets

This file provides basic results about all the `Finset.Ixx`, which are defined in
`Order.Interval.Finset.Defs`.

In addition, it shows that in a locally finite order `≤` and `<` are the transitive closures of,
respectively, `⩿` and `⋖`, which then leads to a characterization of monotone and strictly
functions whose domain is a locally finite order. In particular, this file proves:

* `le_iff_transGen_wcovBy`: `≤` is the transitive closure of `⩿`
* `lt_iff_transGen_covBy`: `<` is the transitive closure of `⋖`
* `monotone_iff_forall_wcovBy`: Characterization of monotone functions
* `strictMono_iff_forall_covBy`: Characterization of strictly monotone functions

## TODO

This file was originally only about `Finset.Ico a b` where `a b : ℕ`. No care has yet been taken to
generalize these lemmas properly and many lemmas about `Icc`, `Ioc`, `Ioo` are missing. In general,
what's to do is taking the lemmas in `Data.X.Intervals` and abstract away the concrete structure.

Complete the API. See
https://github.com/leanprover-community/mathlib/pull/14448#discussion_r906109235
for some ideas.
-/

@[expose] public section

assert_not_exists MonoidWithZero Finset.sum

open Function OrderDual

open FinsetInterval

variable {ι α : Type*} {a a₁ a₂ b b₁ b₂ c x : α}

namespace Finset

section Preorder

variable [Preorder α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α]

@[simp]
/-
**Finset.nonempty_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：nonempty_Icc : (Icc a b).Nonempty ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_nonempty`：coe_nonempty {s : Finset α} : (s : Set α).Nonempty 
↔ s.Nonempty
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Set.nonempty_Icc`：nonempty_Icc : (Icc a b).Nonempty ↔ a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nonempty_Icc : (Icc a b).Nonempty ↔ a ≤ b := by
  rw [← coe_nonempty, coe_Icc, Set.nonempty_Icc]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.nonempty_Icc_of_le⟩ := nonempty_Icc

@[simp]
/-
**Finset.nonempty_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：nonempty_Ico : (Ico a b).Nonempty ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_nonempty`：coe_nonempty {s : Finset α} : (s : Set α).Nonempty 
↔ s.Nonempty
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Set.nonempty_Ico`：nonempty_Ico : (Ico a b).Nonempty ↔ a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nonempty_Ico : (Ico a b).Nonempty ↔ a < b := by
  rw [← coe_nonempty, coe_Ico, Set.nonempty_Ico]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.nonempty_Ico_of_lt⟩ := nonempty_Ico

@[simp]
/-
**Finset.nonempty_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：nonempty_Ioc : (Ioc a b).Nonempty ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_nonempty`：coe_nonempty {s : Finset α} : (s : Set α).Nonempty 
↔ s.Nonempty
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Set.nonempty_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, (Set.I
oc b a).Nonempty ↔ b < a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nonempty_Ioc : (Ioc a b).Nonempty ↔ a < b := by
  rw [← coe_nonempty, coe_Ioc, Set.nonempty_Ioc]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.nonempty_Ioc_of_lt⟩ := nonempty_Ioc

-- TODO: This is nonsense. A locally finite order is never densely ordered;
-- See `not_lt_of_denselyOrdered_of_locallyFinite`
@[simp]
/-
**Finset.nonempty_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_nonempty`：coe_nonempty {s : Finset α} : (s : Set α).Nonempty 
↔ s.Nonempty
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Set.nonempty_Ioo`：nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔
 a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔ a < b := by
  rw [← coe_nonempty, coe_Ioo, Set.nonempty_Ioo]

@[simp]
/-
**Finset.Icc_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_eq_empty_iff : Icc a b = ∅ ↔ ¬a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_eq_empty`：coe_eq_empty {s : Finset α} : (s : Set α) = ∅ ↔ s =
 ∅
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Set.Icc_eq_empty_iff`：Icc_eq_empty_iff : Icc a b = ∅ ↔ ¬a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Icc_eq_empty_iff : Icc a b = ∅ ↔ ¬a ≤ b := by
  rw [← coe_eq_empty, coe_Icc, Set.Icc_eq_empty_iff]

@[simp]
/-
**Finset.Ico_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_eq_empty_iff : Ico a b = ∅ ↔ ¬a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_eq_empty`：coe_eq_empty {s : Finset α} : (s : Set α) = ∅ ↔ s =
 ∅
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Set.Ico_eq_empty_iff`：Ico_eq_empty_iff : Ico a b = ∅ ↔ ¬a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Ico_eq_empty_iff : Ico a b = ∅ ↔ ¬a < b := by
  rw [← coe_eq_empty, coe_Ico, Set.Ico_eq_empty_iff]

@[simp]
/-
**Finset.Ioc_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioc_eq_empty_iff : Ioc a b = ∅ ↔ ¬a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_eq_empty`：coe_eq_empty {s : Finset α} : (s : Set α) = ∅ ↔ s =
 ∅
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Set.Ioc_eq_empty_iff`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Se
t.Ioc b a = ∅ ↔ ¬b < a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Ioc_eq_empty_iff : Ioc a b = ∅ ↔ ¬a < b := by
  rw [← coe_eq_empty, coe_Ioc, Set.Ioc_eq_empty_iff]

-- TODO: This is nonsense. A locally finite order is never densely ordered
-- See `not_lt_of_denselyOrdered_of_locallyFinite`
@[simp]
/-
**Finset.Ioo_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioo_eq_empty_iff [DenselyOrdered α] : Ioo a b = ∅ ↔ ¬a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_eq_empty`：coe_eq_empty {s : Finset α} : (s : Set α) = ∅ ↔ s =
 ∅
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Set.Ioo_eq_empty_iff`：Ioo_eq_empty_iff [DenselyOrdered α] : Ioo a b = ∅ 
↔ ¬a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Ioo_eq_empty_iff [DenselyOrdered α] : Ioo a b = ∅ ↔ ¬a < b := by
  rw [← coe_eq_empty, coe_Ioo, Set.Ioo_eq_empty_iff]

alias ⟨_, Icc_eq_empty⟩ := Icc_eq_empty_iff

alias ⟨_, Ico_eq_empty⟩ := Ico_eq_empty_iff

alias ⟨_, Ioc_eq_empty⟩ := Ioc_eq_empty_iff

@[simp]
/-
**Finset.Ioo_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
参数：h : ¬a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Finse
t α} : s = ∅ ↔ forall x, x ∉ s
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ioo`：mem_Ioo : x in Ioo a b ↔ a < x ∧ x < b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ hx => h ((mem_Ioo.1 hx).1.trans (mem_Ioo.1 hx).2)

@[simp]
/-
**Finset.Icc_eq_empty_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_eq_empty_of_lt (h : b < a) : Icc a b = ∅
参数：h : b < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Icc_eq_empty`：∀ {α : Type u_2} {a b : α} [inst : Preorder α] [ins
t_1 : LocallyFiniteOrder α], ¬a ≤ b → Finset.Icc a b = ∅
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem Icc_eq_empty_of_lt (h : b < a) : Icc a b = ∅ :=
  Icc_eq_empty h.not_ge

@[simp]
/-
**Finset.Ico_eq_empty_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_eq_empty_of_le (h : b <= a) : Ico a b = ∅
参数：h : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Ico_eq_empty`：∀ {α : Type u_2} {a b : α} [inst : Preorder α] [ins
t_1 : LocallyFiniteOrder α], ¬a < b → Finset.Ico a b = ∅
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
-/
theorem Ico_eq_empty_of_le (h : b ≤ a) : Ico a b = ∅ :=
  Ico_eq_empty h.not_gt

@[simp]
/-
**Finset.Ioc_eq_empty_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioc_eq_empty_of_le (h : b <= a) : Ioc a b = ∅
参数：h : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Ioc_eq_empty`：∀ {α : Type u_2} {a b : α} [inst : Preorder α] [ins
t_1 : LocallyFiniteOrder α], ¬a < b → Finset.Ioc a b = ∅
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
-/
theorem Ioc_eq_empty_of_le (h : b ≤ a) : Ioc a b = ∅ :=
  Ioc_eq_empty h.not_gt

@[simp]
/-
**Finset.Ioo_eq_empty_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioo_eq_empty_of_le (h : b <= a) : Ioo a b = ∅
参数：h : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
-/
theorem Ioo_eq_empty_of_le (h : b ≤ a) : Ioo a b = ∅ :=
  Ioo_eq_empty h.not_gt
/-
**Finset.left_mem_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：left_mem_Icc : a in Icc a b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem left_mem_Icc : a ∈ Icc a b ↔ a ≤ b := by simp only [mem_Icc, true_and, le_rfl]
/-
**Finset.left_mem_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：left_mem_Ico : a in Ico a b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem left_mem_Ico : a ∈ Ico a b ↔ a < b := by simp only [mem_Ico, true_and, le_refl]
/-
**Finset.right_mem_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：right_mem_Icc : b in Icc a b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem right_mem_Icc : b ∈ Icc a b ↔ a ≤ b := by simp only [mem_Icc, and_true, le_rfl]
/-
**Finset.right_mem_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：right_mem_Ioc : b in Ioc a b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem right_mem_Ioc : b ∈ Ioc a b ↔ a < b := by simp only [mem_Ioc, and_true, le_rfl]
/-
**Finset.left_notMem_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：left_notMem_Ioc : a ∉ Ioc a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ioc`：mem_Ioc : x in Ioc a b ↔ a < x ∧ x <= b
-/
theorem left_notMem_Ioc : a ∉ Ioc a b := fun h => lt_irrefl _ (mem_Ioc.1 h).1
/-
**Finset.left_notMem_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：left_notMem_Ioo : a ∉ Ioo a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ioo`：mem_Ioo : x in Ioo a b ↔ a < x ∧ x < b
-/
theorem left_notMem_Ioo : a ∉ Ioo a b := fun h => lt_irrefl _ (mem_Ioo.1 h).1
/-
**Finset.right_notMem_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：right_notMem_Ico : b ∉ Ico a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
-/
theorem right_notMem_Ico : b ∉ Ico a b := fun h => lt_irrefl _ (mem_Ico.1 h).2
/-
**Finset.right_notMem_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：right_notMem_Ioo : b ∉ Ioo a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ioo`：mem_Ioo : x in Ioo a b ↔ a < x ∧ x < b
-/
theorem right_notMem_Ioo : b ∉ Ioo a b := fun h => lt_irrefl _ (mem_Ioo.1 h).2

@[gcongr]
/-
**Finset.Icc_subset_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Icc a₁ b₁ subseteq Icc a₂
 b₂
参数：ha : a₂ <= a₁；hb : b₁ <= b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Set.Icc_subset_Icc`：Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Icc
 a₁ b₁ subseteq Icc a₂ b₂
-/
theorem Icc_subset_Icc (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Icc a₁ b₁ ⊆ Icc a₂ b₂ := by
  simpa [← coe_subset] using Set.Icc_subset_Icc ha hb

@[gcongr]
/-
**Finset.Ico_subset_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_subset_Ico (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ico a₁ b₁ subseteq Ico a₂
 b₂
参数：ha : a₂ <= a₁；hb : b₁ <= b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Set.Ico_subset_Ico`：Ico_subset_Ico (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ico
 a₁ b₁ subseteq Ico a₂ b₂
-/
theorem Ico_subset_Ico (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Ico a₁ b₁ ⊆ Ico a₂ b₂ := by
  simpa [← coe_subset] using Set.Ico_subset_Ico ha hb

@[gcongr]
/-
**Finset.Ioc_subset_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioc_subset_Ioc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ioc a₁ b₁ subseteq Ioc a₂
 b₂
参数：ha : a₂ <= a₁；hb : b₁ <= b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Set.Ioc_subset_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b₁ b₂ : 
α}, b₂ ≤ b₁ → a₁ ≤ a₂ → Set.Ioc b₁ a₁ ⊆ Set.Ioc b₂ a₂
-/
theorem Ioc_subset_Ioc (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Ioc a₁ b₁ ⊆ Ioc a₂ b₂ := by
  simpa [← coe_subset] using Set.Ioc_subset_Ioc ha hb

@[gcongr]
/-
**Finset.Ioo_subset_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioo_subset_Ioo (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ioo a₁ b₁ subseteq Ioo a₂
 b₂
参数：ha : a₂ <= a₁；hb : b₁ <= b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Set.Ioo_subset_Ioo`：Ioo_subset_Ioo (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ioo
 a₁ b₁ subseteq Ioo a₂ b₂
-/
theorem Ioo_subset_Ioo (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Ioo a₁ b₁ ⊆ Ioo a₂ b₂ := by
  simpa [← coe_subset] using Set.Ioo_subset_Ioo ha hb
/-
**Finset.Icc_subset_Icc_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_subset_Icc_left (h : a₁ <= a₂) : Icc a₂ b subseteq Icc a₁ b
参数：h : a₁ <= a₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Icc_subset_Icc`：Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : 
Icc a₁ b₁ subseteq Icc a₂ b₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Icc_subset_Icc_left (h : a₁ ≤ a₂) : Icc a₂ b ⊆ Icc a₁ b :=
  Icc_subset_Icc h le_rfl
/-
**Finset.Ico_subset_Ico_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_subset_Ico_left (h : a₁ <= a₂) : Ico a₂ b subseteq Ico a₁ b
参数：h : a₁ <= a₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Ico_subset_Ico`：Ico_subset_Ico (ha : a₂ <= a₁) (hb : b₁ <= b₂) : 
Ico a₁ b₁ subseteq Ico a₂ b₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Ico_subset_Ico_left (h : a₁ ≤ a₂) : Ico a₂ b ⊆ Ico a₁ b :=
  Ico_subset_Ico h le_rfl
/-
**Finset.Ioc_subset_Ioc_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioc_subset_Ioc_left (h : a₁ <= a₂) : Ioc a₂ b subseteq Ioc a₁ b
参数：h : a₁ <= a₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Ioc_subset_Ioc`：Ioc_subset_Ioc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : 
Ioc a₁ b₁ subseteq Ioc a₂ b₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Ioc_subset_Ioc_left (h : a₁ ≤ a₂) : Ioc a₂ b ⊆ Ioc a₁ b :=
  Ioc_subset_Ioc h le_rfl
/-
**Finset.Ioo_subset_Ioo_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioo_subset_Ioo_left (h : a₁ <= a₂) : Ioo a₂ b subseteq Ioo a₁ b
参数：h : a₁ <= a₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Ioo_subset_Ioo`：Ioo_subset_Ioo (ha : a₂ <= a₁) (hb : b₁ <= b₂) : 
Ioo a₁ b₁ subseteq Ioo a₂ b₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Ioo_subset_Ioo_left (h : a₁ ≤ a₂) : Ioo a₂ b ⊆ Ioo a₁ b :=
  Ioo_subset_Ioo h le_rfl
/-
**Finset.Icc_subset_Icc_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_subset_Icc_right (h : b₁ <= b₂) : Icc a b₁ subseteq Icc a b₂
参数：h : b₁ <= b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Icc_subset_Icc`：Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : 
Icc a₁ b₁ subseteq Icc a₂ b₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Icc_subset_Icc_right (h : b₁ ≤ b₂) : Icc a b₁ ⊆ Icc a b₂ :=
  Icc_subset_Icc le_rfl h
/-
**Finset.Ico_subset_Ico_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_subset_Ico_right (h : b₁ <= b₂) : Ico a b₁ subseteq Ico a b₂
参数：h : b₁ <= b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Ico_subset_Ico`：Ico_subset_Ico (ha : a₂ <= a₁) (hb : b₁ <= b₂) : 
Ico a₁ b₁ subseteq Ico a₂ b₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Ico_subset_Ico_right (h : b₁ ≤ b₂) : Ico a b₁ ⊆ Ico a b₂ :=
  Ico_subset_Ico le_rfl h
/-
**Finset.Ioc_subset_Ioc_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioc_subset_Ioc_right (h : b₁ <= b₂) : Ioc a b₁ subseteq Ioc a b₂
参数：h : b₁ <= b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Ioc_subset_Ioc`：Ioc_subset_Ioc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : 
Ioc a₁ b₁ subseteq Ioc a₂ b₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Ioc_subset_Ioc_right (h : b₁ ≤ b₂) : Ioc a b₁ ⊆ Ioc a b₂ :=
  Ioc_subset_Ioc le_rfl h
/-
**Finset.Ioo_subset_Ioo_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioo_subset_Ioo_right (h : b₁ <= b₂) : Ioo a b₁ subseteq Ioo a b₂
参数：h : b₁ <= b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Ioo_subset_Ioo`：Ioo_subset_Ioo (ha : a₂ <= a₁) (hb : b₁ <= b₂) : 
Ioo a₁ b₁ subseteq Ioo a₂ b₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Ioo_subset_Ioo_right (h : b₁ ≤ b₂) : Ioo a b₁ ⊆ Ioo a b₂ :=
  Ioo_subset_Ioo le_rfl h
/-
**Finset.Ico_subset_Ioo_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_subset_Ioo_left (h : a₁ < a₂) : Ico a₂ b subseteq Ioo a₁ b
参数：h : a₁ < a₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Set.Ico_subset_Ioo_left`：Ico_subset_Ioo_left (h : a₁ < a₂) : Ico a₂ b su
bseteq Ioo a₁ b
-/
theorem Ico_subset_Ioo_left (h : a₁ < a₂) : Ico a₂ b ⊆ Ioo a₁ b := by
  rw [← coe_subset, coe_Ico, coe_Ioo]
  exact Set.Ico_subset_Ioo_left h
/-
**Finset.Ioc_subset_Ioo_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioc_subset_Ioo_right (h : b₁ < b₂) : Ioc a b₁ subseteq Ioo a b₂
参数：h : b₁ < b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Set.Ioc_subset_Ioo_right`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b 
: α}, a₂ < a₁ → Set.Ioc b a₂ ⊆ Set.Ioo b a₁
-/
theorem Ioc_subset_Ioo_right (h : b₁ < b₂) : Ioc a b₁ ⊆ Ioo a b₂ := by
  rw [← coe_subset, coe_Ioc, coe_Ioo]
  exact Set.Ioc_subset_Ioo_right h
/-
**Finset.Icc_subset_Ico_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_subset_Ico_right (h : b₁ < b₂) : Icc a b₁ subseteq Ico a b₂
参数：h : b₁ < b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Set.Icc_subset_Ico_right`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b 
: α}, a₂ < a₁ → Set.Icc b a₂ ⊆ Set.Ico b a₁
-/
theorem Icc_subset_Ico_right (h : b₁ < b₂) : Icc a b₁ ⊆ Ico a b₂ := by
  rw [← coe_subset, coe_Icc, coe_Ico]
  exact Set.Icc_subset_Ico_right h
/-
**Finset.Ioo_subset_Ico_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioo_subset_Ico_self : Ioo a b subseteq Ico a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b
-/
theorem Ioo_subset_Ico_self : Ioo a b ⊆ Ico a b := by
  rw [← coe_subset, coe_Ioo, coe_Ico]
  exact Set.Ioo_subset_Ico_self
/-
**Finset.Ioo_subset_Ioc_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioo_subset_Ioc_self : Ioo a b subseteq Ioc a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a
-/
theorem Ioo_subset_Ioc_self : Ioo a b ⊆ Ioc a b := by
  rw [← coe_subset, coe_Ioo, coe_Ioc]
  exact Set.Ioo_subset_Ioc_self
/-
**Finset.Ico_subset_Icc_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_subset_Icc_self : Ico a b subseteq Icc a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
-/
theorem Ico_subset_Icc_self : Ico a b ⊆ Icc a b := by
  rw [← coe_subset, coe_Ico, coe_Icc]
  exact Set.Ico_subset_Icc_self
/-
**Finset.Ioc_subset_Icc_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioc_subset_Icc_self : Ioc a b subseteq Icc a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
-/
theorem Ioc_subset_Icc_self : Ioc a b ⊆ Icc a b := by
  rw [← coe_subset, coe_Ioc, coe_Icc]
  exact Set.Ioc_subset_Icc_self
/-
**Finset.Ioo_subset_Icc_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.Ioo_subset_Ico_self`：Ioo_subset_Ico_self : Ioo a b subseteq Ico a
 b
· 使用定理 `Finset.Ico_subset_Icc_self`：Ico_subset_Icc_self : Ico a b subseteq Icc a
 b
-/
theorem Ioo_subset_Icc_self : Ioo a b ⊆ Icc a b :=
  Ioo_subset_Ico_self.trans Ico_subset_Icc_self
/-
**Finset.Icc_subset_Icc_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_subset_Icc_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ subseteq Icc a₂ b₂ ↔ a₂ <= 
a₁ ∧ b₁ <= b₂
参数：h₁ : a₁ <= b₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Set.Icc_subset_Icc_iff`：Icc_subset_Icc_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ s
ubseteq Icc a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ <= b₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Icc_subset_Icc_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Icc a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ := by
  rw [← coe_subset, coe_Icc, coe_Icc, Set.Icc_subset_Icc_iff h₁]
/-
**Finset.Icc_subset_Ioo_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_subset_Ioo_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ subseteq Ioo a₂ b₂ ↔ a₂ < a
₁ ∧ b₁ < b₂
参数：h₁ : a₁ <= b₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Set.Icc_subset_Ioo_iff`：Icc_subset_Ioo_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ s
ubseteq Ioo a₂ b₂ ↔ a₂ < a₁ ∧ b₁ < b₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Icc_subset_Ioo_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ioo a₂ b₂ ↔ a₂ < a₁ ∧ b₁ < b₂ := by
  rw [← coe_subset, coe_Icc, coe_Ioo, Set.Icc_subset_Ioo_iff h₁]
/-
**Finset.Icc_subset_Ico_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_subset_Ico_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ subseteq Ico a₂ b₂ ↔ a₂ <= 
a₁ ∧ b₁ < b₂
参数：h₁ : a₁ <= b₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Set.Icc_subset_Ico_iff`：Icc_subset_Ico_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ s
ubseteq Ico a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ < b₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Icc_subset_Ico_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ < b₂ := by
  rw [← coe_subset, coe_Icc, coe_Ico, Set.Icc_subset_Ico_iff h₁]
/-
**Finset.Icc_subset_Ioc_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_subset_Ioc_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ subseteq Ioc a₂ b₂ ↔ a₂ < a
₁ ∧ b₁ <= b₂
参数：h₁ : a₁ <= b₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.Icc_subset_Ico_iff`：Icc_subset_Ico_iff (h₁ : a₁ <= b₁) : Icc a₁ b
₁ subseteq Ico a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ < b₂
· 使用定理 `LE.le.dual`：∀ {α : Type u_1} [inst : LE α] {a b : α}, b ≤ a → OrderDual.
toDual a ≤ OrderDual.toDual b
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
theorem Icc_subset_Ioc_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ioc a₂ b₂ ↔ a₂ < a₁ ∧ b₁ ≤ b₂ :=
  (Icc_subset_Ico_iff h₁.dual).trans and_comm

--TODO: `Ico_subset_Ioo_iff`, `Ioc_subset_Ioo_iff`
/-
**Finset.Icc_ssubset_Icc_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_ssubset_Icc_left (hI : a₂ <= b₂) (ha : a₂ < a₁) (hb : b₁ <= b₂) : Icc 
a₁ b₁ ⊂ Icc a₂ b₂
参数：hI : a₂ <= b₂；ha : a₂ < a₁；hb : b₁ <= b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_ssubset`：coe_ssubset {s₁ s₂ : Finset α} : (s₁ : Set α) ⊂ s₂ ↔
 s₁ ⊂ s₂
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Set.Icc_ssubset_Icc_left`：Icc_ssubset_Icc_left (h₂ : a₂ <= b₂) (ha : a₂ 
< a₁) (hb : b₁ <= b₂) : Icc a₁ b₁ ⊂ Icc a₂ b₂
-/
theorem Icc_ssubset_Icc_left (hI : a₂ ≤ b₂) (ha : a₂ < a₁) (hb : b₁ ≤ b₂) :
    Icc a₁ b₁ ⊂ Icc a₂ b₂ := by
  rw [← coe_ssubset, coe_Icc, coe_Icc]
  exact Set.Icc_ssubset_Icc_left hI ha hb
/-
**Finset.Icc_ssubset_Icc_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_ssubset_Icc_right (hI : a₂ <= b₂) (ha : a₂ <= a₁) (hb : b₁ < b₂) : Icc
 a₁ b₁ ⊂ Icc a₂ b₂
参数：hI : a₂ <= b₂；ha : a₂ <= a₁；hb : b₁ < b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_ssubset`：coe_ssubset {s₁ s₂ : Finset α} : (s₁ : Set α) ⊂ s₂ ↔
 s₁ ⊂ s₂
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Set.Icc_ssubset_Icc_right`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b
₁ b₂ : α}, b₂ ≤ a₂ → b₂ ≤ b₁ → a₁ < a₂ → Set.Icc b₁ a₁ ⊂ Set.Icc b₂ a₂
-/
theorem Icc_ssubset_Icc_right (hI : a₂ ≤ b₂) (ha : a₂ ≤ a₁) (hb : b₁ < b₂) :
    Icc a₁ b₁ ⊂ Icc a₂ b₂ := by
  rw [← coe_ssubset, coe_Icc, coe_Icc]
  exact Set.Icc_ssubset_Icc_right hI ha hb

@[simp]
/-
**Finset.Ioc_disjoint_Ioc_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioc_disjoint_Ioc_of_le {d : α} (hbc : b <= c) : Disjoint (Ioc a b) (Ioc c 
d)
参数：hbc : b <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `not_and_of_not_left`：∀ {a : Prop} (b : Prop), ¬a → ¬(a ∧ b)
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ioc`：mem_Ioc : x in Ioc a b ↔ a < x ∧ x <= b
-/
theorem Ioc_disjoint_Ioc_of_le {d : α} (hbc : b ≤ c) : Disjoint (Ioc a b) (Ioc c d) :=
  disjoint_left.2 fun _ h1 h2 ↦ not_and_of_not_left _
    ((mem_Ioc.1 h1).2.trans hbc).not_gt (mem_Ioc.1 h2)
/-
**Finset._root_.not_lt_of_denselyOrdered_of_locallyFinite** 是 Mathlib 中的一个引理，位于命
名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.not_lt_of_denselyOrdered_of_locallyFinite [DenselyOrdered α] (a b : α) :
    ¬ a < b := by
  intro h
  induction hs : Finset.Icc a b using Finset.strongInduction generalizing b with | H i ih
  subst hs
  obtain ⟨c, hac, hcb⟩ := exists_between h
  refine ih _ ?_ c hac rfl
  exact Finset.Icc_ssubset_Icc_right (hac.trans hcb).le le_rfl hcb

variable (a)
/-
**Finset.Ico_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_self : Ico a a = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Ico_eq_empty`：∀ {α : Type u_2} {a b : α} [inst : Preorder α] [ins
t_1 : LocallyFiniteOrder α], ¬a < b → Finset.Ico a b = ∅
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
-/
theorem Ico_self : Ico a a = ∅ :=
  Ico_eq_empty <| lt_irrefl _
/-
**Finset.Ioc_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioc_self : Ioc a a = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Ioc_eq_empty`：∀ {α : Type u_2} {a b : α} [inst : Preorder α] [ins
t_1 : LocallyFiniteOrder α], ¬a < b → Finset.Ioc a b = ∅
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
-/
theorem Ioc_self : Ioc a a = ∅ :=
  Ioc_eq_empty <| lt_irrefl _
/-
**Finset.Ioo_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioo_self : Ioo a a = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
-/
theorem Ioo_self : Ioo a a = ∅ :=
  Ioo_eq_empty <| lt_irrefl _

variable {a}

/-- A set with upper and lower bounds in a locally finite order is a fintype -/
@[instance_reducible]
/-
**Finset._root_.Set.fintypeOfMemBounds** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set with upper and lower bounds in a locally finite order is a fintype
-/
def _root_.Set.fintypeOfMemBounds {s : Set α} [DecidablePred (· ∈ s)] (ha : a ∈ lowerBounds s)
    (hb : b ∈ upperBounds s) : Fintype s :=
  Set.fintypeSubset (Set.Icc a b) fun _ hx => ⟨ha hx, hb hx⟩

section Filter

/-
**Finset.Ico_filter_lt_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_filter_lt_of_le_left [DecidablePred (· < c)] (hca : c <= a) : {x in Ic
o a b | x < c} = ∅
参数：· < c；hca : c <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.filter_false_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Deci
dablePred p] {s : Finset α}, (∀ x ∈ s, ¬p x) → Finset.filter p s = ∅
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
-/
theorem Ico_filter_lt_of_le_left [DecidablePred (· < c)] (hca : c ≤ a) :
    {x ∈ Ico a b | x < c} = ∅ :=
  filter_false_of_mem fun _ hx => (hca.trans (mem_Ico.1 hx).1).not_gt
/-
**Finset.Ico_filter_lt_of_right_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_filter_lt_of_right_le [DecidablePred (· < c)] (hbc : b <= c) : {x in I
co a b | x < c} = Ico a b
参数：· < c；hbc : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.filter_true_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Decid
ablePred p] {s : Finset α}, (∀ x ∈ s, p x) → Finset.filter p s = s
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
-/
theorem Ico_filter_lt_of_right_le [DecidablePred (· < c)] (hbc : b ≤ c) :
    {x ∈ Ico a b | x < c} = Ico a b :=
  filter_true_of_mem fun _ hx => (mem_Ico.1 hx).2.trans_le hbc
/-
**Finset.Ico_filter_lt_of_le_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_filter_lt_of_le_right [DecidablePred (· < c)] (hcb : c <= b) : {x in I
co a b | x < c} = Ico a c
参数：· < c；hcb : c <= b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ico_filter_lt_of_le_right [DecidablePred (· < c)] (hcb : c ≤ b) :
    {x ∈ Ico a b | x < c} = Ico a c := by
  grind
/-
**Finset.Ico_filter_le_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_filter_le_of_le_left {a b c : α} [DecidablePred (c <= ·)] (hca : c <= 
a) : {x in Ico a b | c <= x} = Ico a b
参数：c <= ·；hca : c <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.filter_true_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Decid
ablePred p] {s : Finset α}, (∀ x ∈ s, p x) → Finset.filter p s = s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
-/
theorem Ico_filter_le_of_le_left {a b c : α} [DecidablePred (c ≤ ·)] (hca : c ≤ a) :
    {x ∈ Ico a b | c ≤ x} = Ico a b :=
  filter_true_of_mem fun _ hx => hca.trans (mem_Ico.1 hx).1
/-
**Finset.Ico_filter_le_of_right_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_filter_le_of_right_le {a b : α} [DecidablePred (b <= ·)] : {x in Ico a
 b | b <= x} = ∅
参数：b <= ·。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.filter_false_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Deci
dablePred p] {s : Finset α}, (∀ x ∈ s, ¬p x) → Finset.filter p s = ∅
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
-/
theorem Ico_filter_le_of_right_le {a b : α} [DecidablePred (b ≤ ·)] :
    {x ∈ Ico a b | b ≤ x} = ∅ :=
  filter_false_of_mem fun _ hx => (mem_Ico.1 hx).2.not_ge
/-
**Finset.Ico_filter_le_of_left_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_filter_le_of_left_le {a b c : α} [DecidablePred (c <= ·)] (hac : a <= 
c) : {x in Ico a b | c <= x} = Ico c b
参数：c <= ·；hac : a <= c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ico_filter_le_of_left_le {a b c : α} [DecidablePred (c ≤ ·)] (hac : a ≤ c) :
    {x ∈ Ico a b | c ≤ x} = Ico c b := by
  grind
/-
**Finset.Icc_filter_lt_of_lt_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_filter_lt_of_lt_right {a b c : α} [DecidablePred (· < c)] (h : b < c) 
: {x in Icc a b | x < c} = Icc a b
参数：· < c；h : b < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.filter_true_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Decid
ablePred p] {s : Finset α}, (∀ x ∈ s, p x) → Finset.filter p s = s
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Icc`：mem_Icc : x in Icc a b ↔ a <= x ∧ x <= b
-/
theorem Icc_filter_lt_of_lt_right {a b c : α} [DecidablePred (· < c)] (h : b < c) :
    {x ∈ Icc a b | x < c} = Icc a b :=
  filter_true_of_mem fun _ hx => lt_of_le_of_lt (mem_Icc.1 hx).2 h
/-
**Finset.Ioc_filter_lt_of_lt_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioc_filter_lt_of_lt_right {a b c : α} [DecidablePred (· < c)] (h : b < c) 
: {x in Ioc a b | x < c} = Ioc a b
参数：· < c；h : b < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.filter_true_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Decid
ablePred p] {s : Finset α}, (∀ x ∈ s, p x) → Finset.filter p s = s
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ioc`：mem_Ioc : x in Ioc a b ↔ a < x ∧ x <= b
-/
theorem Ioc_filter_lt_of_lt_right {a b c : α} [DecidablePred (· < c)] (h : b < c) :
    {x ∈ Ioc a b | x < c} = Ioc a b :=
  filter_true_of_mem fun _ hx => lt_of_le_of_lt (mem_Ioc.1 hx).2 h
/-
**Finset.Iic_filter_lt_of_lt_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Iic_filter_lt_of_lt_right {α} [Preorder α] [LocallyFiniteOrderBot α] {a c 
: α} [DecidablePred (· < c)] (h : a < c) : {x in Iic a | x < c} = Iic a
参数：· < c；h : a < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.filter_true_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Decid
ablePred p] {s : Finset α}, (∀ x ∈ s, p x) → Finset.filter p s = s
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
-/
theorem Iic_filter_lt_of_lt_right {α} [Preorder α] [LocallyFiniteOrderBot α] {a c : α}
    [DecidablePred (· < c)] (h : a < c) : {x ∈ Iic a | x < c} = Iic a :=
  filter_true_of_mem fun _ hx => lt_of_le_of_lt (mem_Iic.1 hx) h

variable (a b) [Fintype α]
/-
**Finset.filter_lt_lt_eq_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_lt_lt_eq_Ioo [DecidablePred fun j => a < j ∧ j < b] : ({j | a < j ∧
 j < b} : Finset _) = Ioo a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem filter_lt_lt_eq_Ioo [DecidablePred fun j => a < j ∧ j < b] :
    ({j | a < j ∧ j < b} : Finset _) = Ioo a b := by ext; simp
/-
**Finset.filter_lt_le_eq_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_lt_le_eq_Ioc [DecidablePred fun j => a < j ∧ j <= b] : ({j | a < j 
∧ j <= b} : Finset _) = Ioc a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem filter_lt_le_eq_Ioc [DecidablePred fun j => a < j ∧ j ≤ b] :
    ({j | a < j ∧ j ≤ b} : Finset _) = Ioc a b := by ext; simp
/-
**Finset.filter_le_lt_eq_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_le_lt_eq_Ico [DecidablePred fun j => a <= j ∧ j < b] : ({j | a <= j
 ∧ j < b} : Finset _) = Ico a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem filter_le_lt_eq_Ico [DecidablePred fun j => a ≤ j ∧ j < b] :
    ({j | a ≤ j ∧ j < b} : Finset _) = Ico a b := by ext; simp
/-
**Finset.filter_le_le_eq_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_le_le_eq_Icc [DecidablePred fun j => a <= j ∧ j <= b] : ({j | a <= 
j ∧ j <= b} : Finset _) = Icc a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem filter_le_le_eq_Icc [DecidablePred fun j => a ≤ j ∧ j ≤ b] :
    ({j | a ≤ j ∧ j ≤ b} : Finset _) = Icc a b := by ext; simp

end Filter

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α]

@[simp]
/-
**Finset.Ioi_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioi_eq_empty : Ioi a = ∅ ↔ IsMax a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_eq_empty`：coe_eq_empty {s : Finset α} : (s : Set α) = ∅ ↔ s =
 ∅
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `Set.Ioi_eq_empty_iff`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, Set.
Ioi a = ∅ ↔ IsMax a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Ioi_eq_empty : Ioi a = ∅ ↔ IsMax a := by
  rw [← coe_eq_empty, coe_Ioi, Set.Ioi_eq_empty_iff]

@[simp] alias ⟨_, _root_.IsMax.finsetIoi_eq⟩ := Ioi_eq_empty
/-
**Finset.Ioi_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {a : α} [inst : Preorder α] [inst_1 : LocallyFiniteOrderT
op α], (Finset.Ioi a).Nonempty ↔ ¬IsMax a
参数：Finset.Ioi a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₃`：contrapose_iff₃ {p q : Prop} 
: (¬ p ↔ q) -> (p ↔ ¬ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Ioi_eq_empty`：Ioi_eq_empty : Ioi a = ∅ ↔ IsMax a
-/
@[simp] lemma Ioi_nonempty : (Ioi a).Nonempty ↔ ¬ IsMax a := by
  contrapose!; exact Ioi_eq_empty
/-
**Finset.Ioi_top** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioi_top [OrderTop α] : Ioi (⊤ : α) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.Ioi_eq_empty`：Ioi_eq_empty : Ioi a = ∅ ↔ IsMax a
· 使用定理 `isMax_top`：isMax_top : IsMax (⊤ : α)
-/
theorem Ioi_top [OrderTop α] : Ioi (⊤ : α) = ∅ := Ioi_eq_empty.mpr isMax_top

@[simp]
/-
**Finset.Ici_bot** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ici_bot [OrderBot α] [Fintype α] : Ici (⊥ : α) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Ici_bot [OrderBot α] [Fintype α] : Ici (⊥ : α) = univ := by
  ext a; simp only [mem_Ici, bot_le, mem_univ]

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
/-
**Finset.nonempty_Ici** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：nonempty_Ici : (Ici a).Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Ici`：mem_Ici : x in Ici a ↔ a <= x
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma nonempty_Ici : (Ici a).Nonempty := ⟨a, mem_Ici.2 le_rfl⟩
/-
**Finset.nonempty_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：nonempty_Ioi : (Ioi a).Nonempty ↔ ¬ IsMax a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma nonempty_Ioi : (Ioi a).Nonempty ↔ ¬ IsMax a := by simp [Finset.Nonempty]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.nonempty_Ioi_of_not_isMax⟩ := nonempty_Ioi

@[simp, gcongr]
/-
**Finset.Ici_subset_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ici_subset_Ici : Ici a subseteq Ici b ↔ b <= a
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
· 使用定理 `Finset.coe_Ici`：coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Ici_subset_Ici : Ici a ⊆ Ici b ↔ b ≤ a := by
  simp [← coe_subset]

@[simp, gcongr]
/-
**Finset.Ici_ssubset_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ici_ssubset_Ici : Ici a ⊂ Ici b ↔ b < a
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
· 使用定理 `Finset.coe_Ici`：coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Ici_ssubset_Ici : Ici a ⊂ Ici b ↔ b < a := by
  simp [← coe_ssubset]

@[gcongr]
/-
**Finset.Ioi_subset_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioi_subset_Ioi (h : a <= b) : Ioi b subseteq Ioi a
参数：h : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `Set.Ioi_subset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ≤ 
a → Set.Ioi a ⊆ Set.Ioi b
-/
theorem Ioi_subset_Ioi (h : a ≤ b) : Ioi b ⊆ Ioi a := by
  simpa [← coe_subset] using Set.Ioi_subset_Ioi h

@[gcongr]
/-
**Finset.Ioi_ssubset_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioi_ssubset_Ioi (h : a < b) : Ioi b ⊂ Ioi a
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `Set.Ioi_ssubset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b <
 a → Set.Ioi a ⊂ Set.Ioi b
-/
theorem Ioi_ssubset_Ioi (h : a < b) : Ioi b ⊂ Ioi a := by
  simpa [← coe_ssubset] using Set.Ioi_ssubset_Ioi h

variable [LocallyFiniteOrder α]
/-
**Finset.Icc_subset_Ici_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_subset_Ici_self : Icc a b subseteq Ici a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Finset.coe_Ici`：coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a
· 使用定理 `Set.Icc_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc b a ⊆ Set.Ici b
-/
theorem Icc_subset_Ici_self : Icc a b ⊆ Ici a := by
  simpa [← coe_subset] using Set.Icc_subset_Ici_self
/-
**Finset.Ico_subset_Ici_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_subset_Ici_self : Ico a b subseteq Ici a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Finset.coe_Ici`：coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a
· 使用定理 `Set.Ico_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Ici b
-/
theorem Ico_subset_Ici_self : Ico a b ⊆ Ici a := by
  simpa [← coe_subset] using Set.Ico_subset_Ici_self
/-
**Finset.Ioc_subset_Ioi_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioc_subset_Ioi_self : Ioc a b subseteq Ioi a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `Set.Ioc_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc b a ⊆ Set.Ioi b
-/
theorem Ioc_subset_Ioi_self : Ioc a b ⊆ Ioi a := by
  simpa [← coe_subset] using Set.Ioc_subset_Ioi_self
/-
**Finset.Ioo_subset_Ioi_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioo_subset_Ioi_self : Ioo a b subseteq Ioi a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `Set.Ioo_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioi b
-/
theorem Ioo_subset_Ioi_self : Ioo a b ⊆ Ioi a := by
  simpa [← coe_subset] using Set.Ioo_subset_Ioi_self
/-
**Finset.Ioc_subset_Ici_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioc_subset_Ici_self : Ioc a b subseteq Ici a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.Ioc_subset_Icc_self`：Ioc_subset_Icc_self : Ioc a b subseteq Icc a
 b
· 使用定理 `Finset.Icc_subset_Ici_self`：Icc_subset_Ici_self : Icc a b subseteq Ici a
-/
theorem Ioc_subset_Ici_self : Ioc a b ⊆ Ici a :=
  Ioc_subset_Icc_self.trans Icc_subset_Ici_self
/-
**Finset.Ioo_subset_Ici_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioo_subset_Ici_self : Ioo a b subseteq Ici a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.Ioo_subset_Ico_self`：Ioo_subset_Ico_self : Ioo a b subseteq Ico a
 b
· 使用定理 `Finset.Ico_subset_Ici_self`：Ico_subset_Ici_self : Ico a b subseteq Ici a
-/
theorem Ioo_subset_Ici_self : Ioo a b ⊆ Ici a :=
  Ioo_subset_Ico_self.trans Ico_subset_Ici_self

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α]

@[simp]
/-
**Finset.Iio_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Iio_eq_empty : Iio a = ∅ ↔ IsMin a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Ioi_eq_empty`：Ioi_eq_empty : Ioi a = ∅ ↔ IsMax a
-/
theorem Iio_eq_empty : Iio a = ∅ ↔ IsMin a := Ioi_eq_empty (α := αᵒᵈ)

@[simp] alias ⟨_, _root_.IsMin.finsetIio_eq⟩ := Iio_eq_empty
/-
**Finset.Iio_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {a : α} [inst : Preorder α] [inst_1 : LocallyFiniteOrderB
ot α], (Finset.Iio a).Nonempty ↔ ¬IsMin a
参数：Finset.Iio a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₃`：contrapose_iff₃ {p q : Prop} 
: (¬ p ↔ q) -> (p ↔ ¬ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Iio_eq_empty`：Iio_eq_empty : Iio a = ∅ ↔ IsMin a
-/
@[simp] lemma Iio_nonempty : (Iio a).Nonempty ↔ ¬ IsMin a := by
  contrapose!; exact Iio_eq_empty
/-
**Finset.Iio_bot** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Iio_bot [OrderBot α] : Iio (⊥ : α) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.Iio_eq_empty`：Iio_eq_empty : Iio a = ∅ ↔ IsMin a
· 使用定理 `isMin_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α], IsM
in ⊥
-/
theorem Iio_bot [OrderBot α] : Iio (⊥ : α) = ∅ := Iio_eq_empty.mpr isMin_bot

@[simp]
/-
**Finset.Iic_top** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Iic_top [OrderTop α] [Fintype α] : Iic (⊤ : α) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Iic_top [OrderTop α] [Fintype α] : Iic (⊤ : α) = univ := by
  ext a; simp only [mem_Iic, le_top, mem_univ]

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
/-
**Finset.nonempty_Iic** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：nonempty_Iic : (Iic a).Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma nonempty_Iic : (Iic a).Nonempty := ⟨a, mem_Iic.2 le_rfl⟩
/-
**Finset.nonempty_Iio** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：nonempty_Iio : (Iio a).Nonempty ↔ ¬ IsMin a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma nonempty_Iio : (Iio a).Nonempty ↔ ¬ IsMin a := by simp [Finset.Nonempty]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.nonempty_Iio_of_not_isMin⟩ := nonempty_Iio

@[simp, gcongr]
/-
**Finset.Iic_subset_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
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
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Iic_subset_Iic : Iic a ⊆ Iic b ↔ a ≤ b := by
  simp [← coe_subset]

@[simp, gcongr]
/-
**Finset.Iic_ssubset_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Iic_ssubset_Iic : Iic a ⊂ Iic b ↔ a < b
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
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Iic_ssubset_Iic : Iic a ⊂ Iic b ↔ a < b := by
  simp [← coe_ssubset]

@[gcongr]
/-
**Finset.Iio_subset_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Iio_subset_Iio (h : a <= b) : Iio a subseteq Iio b
参数：h : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `Set.Iio_subset_Iio`：Iio_subset_Iio (h : a <= b) : Iio a subseteq Iio b
-/
theorem Iio_subset_Iio (h : a ≤ b) : Iio a ⊆ Iio b := by
  simpa [← coe_subset] using Set.Iio_subset_Iio h

@[gcongr]
/-
**Finset.Iio_ssubset_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Iio_ssubset_Iio (h : a < b) : Iio a ⊂ Iio b
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `Set.Iio_ssubset_Iio`：Iio_ssubset_Iio (h : a < b) : Iio a ⊂ Iio b
-/
theorem Iio_ssubset_Iio (h : a < b) : Iio a ⊂ Iio b := by
  simpa [← coe_ssubset] using Set.Iio_ssubset_Iio h
/-
**Finset.sup_Iic_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_Iic_of_monotone {β : Type*} [SemilatticeSup β] [OrderBot β] {f : α -> 
β} (hf : Monotone f) : (Iic a).sup f = f a
参数：hf : Monotone f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.sup_le_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   s.sup f ≤ a ↔ ∀
 b ∈ s,…
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem sup_Iic_of_monotone {β : Type*} [SemilatticeSup β] [OrderBot β] {f : α → β}
    (hf : Monotone f) : (Iic a).sup f = f a :=
  le_antisymm (Finset.sup_le_iff.mpr fun _ h ↦ hf (by simpa using h)) (le_sup (by simp))

variable [LocallyFiniteOrder α]
/-
**Finset.Icc_subset_Iic_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_subset_Iic_self : Icc a b subseteq Iic b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `Set.Icc_subset_Iic_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc a b ⊆ Set.Iic b
-/
theorem Icc_subset_Iic_self : Icc a b ⊆ Iic b := by
  simpa [← coe_subset] using Set.Icc_subset_Iic_self
/-
**Finset.Ioc_subset_Iic_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioc_subset_Iic_self : Ioc a b subseteq Iic b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `Set.Ioc_subset_Iic_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Iic b
-/
theorem Ioc_subset_Iic_self : Ioc a b ⊆ Iic b := by
  simpa [← coe_subset] using Set.Ioc_subset_Iic_self
/-
**Finset.Ico_subset_Iio_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_subset_Iio_self : Ico a b subseteq Iio b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `Set.Ico_subset_Iio_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico a b ⊆ Set.Iio b
-/
theorem Ico_subset_Iio_self : Ico a b ⊆ Iio b := by
  simpa [← coe_subset] using Set.Ico_subset_Iio_self
/-
**Finset.Ioo_subset_Iio_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioo_subset_Iio_self : Ioo a b subseteq Iio b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `Set.Ioo_subset_Iio_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Iio b
-/
theorem Ioo_subset_Iio_self : Ioo a b ⊆ Iio b := by
  simpa [← coe_subset] using Set.Ioo_subset_Iio_self
/-
**Finset.Ico_subset_Iic_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_subset_Iic_self : Ico a b subseteq Iic b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.Ico_subset_Icc_self`：Ico_subset_Icc_self : Ico a b subseteq Icc a
 b
· 使用定理 `Finset.Icc_subset_Iic_self`：Icc_subset_Iic_self : Icc a b subseteq Iic b
-/
theorem Ico_subset_Iic_self : Ico a b ⊆ Iic b :=
  Ico_subset_Icc_self.trans Icc_subset_Iic_self
/-
**Finset.Ioo_subset_Iic_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioo_subset_Iic_self : Ioo a b subseteq Iic b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.Ioo_subset_Ioc_self`：Ioo_subset_Ioc_self : Ioo a b subseteq Ioc a
 b
· 使用定理 `Finset.Ioc_subset_Iic_self`：Ioc_subset_Iic_self : Ioc a b subseteq Iic b
-/
theorem Ioo_subset_Iic_self : Ioo a b ⊆ Iic b :=
  Ioo_subset_Ioc_self.trans Ioc_subset_Iic_self
/-
**Finset.Iic_disjoint_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Iic_disjoint_Ioc (h : a <= b) : Disjoint (Iic a) (Ioc b c)
参数：h : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_Ioc`：mem_Ioc : x in Ioc a b ↔ a < x ∧ x <= b
-/
theorem Iic_disjoint_Ioc (h : a ≤ b) : Disjoint (Iic a) (Ioc b c) :=
  disjoint_left.2 fun _ hax hbcx ↦ (mem_Iic.1 hax).not_gt <| lt_of_le_of_lt h (mem_Ioc.1 hbcx).1

/-- An equivalence between `Finset.Iic a` and `Set.Iic a`. -/
/-
**Finset._root_.Equiv.IicFinsetSet** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence between `Finset.Iic a` and `Set.Iic a`.
-/
def _root_.Equiv.IicFinsetSet (a : α) : Iic a ≃ Set.Iic a where
  toFun b := ⟨b.1, coe_Iic a ▸ mem_coe.2 b.2⟩
  invFun b := ⟨b.1, by rw [← mem_coe, coe_Iic a]; exact b.2⟩

end LocallyFiniteOrderBot

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α] {a : α}

/-
**Finset.Ioi_subset_Ici_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioi_subset_Ici_self : Ioi a subseteq Ici a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ioi`：coe_Ioi (a : α) : (Ioi a : Set α) = Set.Ioi a
· 使用定理 `Finset.coe_Ici`：coe_Ici (a : α) : (Ici a : Set α) = Set.Ici a
· 使用定理 `Set.Ioi_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, S
et.Ioi a ⊆ Set.Ici a
-/
theorem Ioi_subset_Ici_self : Ioi a ⊆ Ici a := by
  simpa [← coe_subset] using Set.Ioi_subset_Ici_self
/-
**Finset._root_.BddBelow.finite** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.BddBelow.finite {s : Set α} (hs : BddBelow s) : s.Finite :=
  let ⟨a, ha⟩ := hs
  (Ici a).finite_toSet.subset fun _ hx => mem_Ici.2 <| ha hx
/-
**Finset._root_.Set.Infinite.not_bddBelow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.Infinite.not_bddBelow {s : Set α} : s.Infinite → ¬BddBelow s :=
  mt BddBelow.finite

variable [Fintype α]
/-
**Finset.filter_lt_eq_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_lt_eq_Ioi [DecidablePred (a < ·)] : ({x | a < x} : Finset _) = Ioi 
a
参数：a < ·。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem filter_lt_eq_Ioi [DecidablePred (a < ·)] : ({x | a < x} : Finset _) = Ioi a := by ext; simp
/-
**Finset.filter_le_eq_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_le_eq_Ici [DecidablePred (a <= ·)] : ({x | a <= x} : Finset _) = Ic
i a
参数：a <= ·。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem filter_le_eq_Ici [DecidablePred (a ≤ ·)] : ({x | a ≤ x} : Finset _) = Ici a := by ext; simp

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α] {a : α}

/-
**Finset.Iio_subset_Iic_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Iio_subset_Iic_self : Iio a subseteq Iic a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `Finset.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iic a) = Set.Iic a
· 使用定理 `Set.Iio_subset_Iic_self`：Iio_subset_Iic_self : Iio a subseteq Iic a
-/
theorem Iio_subset_Iic_self : Iio a ⊆ Iic a := by
  simpa [← coe_subset] using Set.Iio_subset_Iic_self
/-
**Finset._root_.BddAbove.finite** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.BddAbove.finite {s : Set α} (hs : BddAbove s) : s.Finite :=
  hs.dual.finite
/-
**Finset._root_.Set.Infinite.not_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.Infinite.not_bddAbove {s : Set α} : s.Infinite → ¬BddAbove s :=
  mt BddAbove.finite

variable [Fintype α]
/-
**Finset.filter_gt_eq_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_gt_eq_Iio [DecidablePred (· < a)] : ({x | x < a} : Finset _) = Iio 
a
参数：· < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem filter_gt_eq_Iio [DecidablePred (· < a)] : ({x | x < a} : Finset _) = Iio a := by ext; simp
/-
**Finset.filter_ge_eq_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_ge_eq_Iic [DecidablePred (· <= a)] : ({x | x <= a} : Finset _) = Ii
c a
参数：· <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem filter_ge_eq_Iic [DecidablePred (· ≤ a)] : ({x | x ≤ a} : Finset _) = Iic a := by ext; simp

end LocallyFiniteOrderBot

section LocallyFiniteOrder

variable [LocallyFiniteOrder α]

@[simp]
/-
**Finset.Icc_bot** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_bot [OrderBot α] : Icc (⊥ : α) a = Iic a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Icc_bot [OrderBot α] : Icc (⊥ : α) a = Iic a := rfl

@[simp]
/-
**Finset.Icc_top** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_top [OrderTop α] : Icc a (⊤ : α) = Ici a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Icc_top [OrderTop α] : Icc a (⊤ : α) = Ici a := rfl

@[simp]
/-
**Finset.Ico_bot** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_bot [OrderBot α] : Ico (⊥ : α) a = Iio a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ico_bot [OrderBot α] : Ico (⊥ : α) a = Iio a := rfl

@[simp]
/-
**Finset.Ioc_top** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioc_top [OrderTop α] : Ioc a (⊤ : α) = Ioi a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioc_top [OrderTop α] : Ioc a (⊤ : α) = Ioi a := rfl
/-
**Finset.Icc_bot_top** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_bot_top [BoundedOrder α] [Fintype α] : Icc (⊥ : α) (⊤ : α) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Icc_bot`：Icc_bot [OrderBot α] : Icc (⊥ : α) a = Iic a
· 使用定理 `Finset.Iic_top`：Iic_top [OrderTop α] [Fintype α] : Iic (⊤ : α) = univ
-/
theorem Icc_bot_top [BoundedOrder α] [Fintype α] : Icc (⊥ : α) (⊤ : α) = univ := by
  rw [Icc_bot, Iic_top]

end LocallyFiniteOrder

variable [LocallyFiniteOrderTop α] [LocallyFiniteOrderBot α]

/-
**Finset.disjoint_Ioi_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_Ioi_Iio (a : α) : Disjoint (Ioi a) (Iio a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ioi`：mem_Ioi : x in Ioi a ↔ a < x
· 使用定理 `Finset.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iio a ↔ x < a
-/
theorem disjoint_Ioi_Iio (a : α) : Disjoint (Ioi a) (Iio a) :=
  disjoint_left.2 fun _ hab hba => (mem_Ioi.1 hab).not_gt <| mem_Iio.1 hba

end Preorder

section PartialOrder

variable [PartialOrder α] [LocallyFiniteOrder α] {a b c : α}

@[simp]
/-
**Finset.Icc_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_self (a : α) : Icc a a = {a}
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_eq_singleton`：coe_eq_singleton {s : Finset α} {a : α} : (s : 
Set α) = {a} ↔ s = {a}
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
-/
theorem Icc_self (a : α) : Icc a a = {a} := by rw [← coe_eq_singleton, coe_Icc, Set.Icc_self]

@[simp]
/-
**Finset.Icc_eq_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_eq_singleton_iff : Icc a b = {c} ↔ a = c ∧ b = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_eq_singleton`：coe_eq_singleton {s : Finset α} {a : α} : (s : 
Set α) = {a} ↔ s = {a}
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Set.Icc_eq_singleton_iff`：Icc_eq_singleton_iff : Icc a b = {c} ↔ a = c ∧
 b = c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Icc_eq_singleton_iff : Icc a b = {c} ↔ a = c ∧ b = c := by
  rw [← coe_eq_singleton, coe_Icc, Set.Icc_eq_singleton_iff]
/-
**Finset.Ico_disjoint_Ico_consecutive** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_disjoint_Ico_consecutive (a b c : α) : Disjoint (Ico a b) (Ico b c)
参数：a b c : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Ico_disjoint_Ico_consecutive (a b c : α) : Disjoint (Ico a b) (Ico b c) :=
  disjoint_left.2 fun _ hab hbc => (mem_Ico.mp hab).2.not_ge (mem_Ico.mp hbc).1

@[simp]
/-
**Finset.Ici_top** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ici_top [OrderTop α] : Ici (⊤ : α) = {⊤}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.Icc_eq_singleton_iff`：Icc_eq_singleton_iff : Icc a b = {c} ↔ a = 
c ∧ b = c
-/
theorem Ici_top [OrderTop α] : Ici (⊤ : α) = {⊤} := Icc_eq_singleton_iff.2 ⟨rfl, rfl⟩

@[simp]
/-
**Finset.Iic_bot** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Iic_bot [OrderBot α] : Iic (⊥ : α) = {⊥}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.Icc_eq_singleton_iff`：Icc_eq_singleton_iff : Icc a b = {c} ↔ a = 
c ∧ b = c
-/
theorem Iic_bot [OrderBot α] : Iic (⊥ : α) = {⊥} := Icc_eq_singleton_iff.2 ⟨rfl, rfl⟩
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [OrderBot α] : Unique (Iic (⊥ : α)) := by
  rw [Iic_bot]
  infer_instance

section DecidableEq

variable [DecidableEq α]

@[simp]
/-
**Finset.Icc_erase_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_erase_left (a b : α) : (Icc a b).erase a = Ioc a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_erase`：coe_erase (a : α) (s : Finset α) : ↑(erase s a) = (s \
 {a} : Set α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Set.Icc_sdiff_left`：Icc_sdiff_left : Icc a b \ {a} = Ioc a b
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Icc_erase_left (a b : α) : (Icc a b).erase a = Ioc a b := by simp [← coe_inj]

@[simp]
/-
**Finset.Icc_erase_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_erase_right (a b : α) : (Icc a b).erase b = Ico a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_erase`：coe_erase (a : α) (s : Finset α) : ↑(erase s a) = (s \
 {a} : Set α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Set.Icc_sdiff_right`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α},
 Set.Icc b a \ {a} = Set.Ico b a
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Icc_erase_right (a b : α) : (Icc a b).erase b = Ico a b := by simp [← coe_inj]

@[simp]
/-
**Finset.Ico_erase_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_erase_left (a b : α) : (Ico a b).erase a = Ioo a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_erase`：coe_erase (a : α) (s : Finset α) : ↑(erase s a) = (s \
 {a} : Set α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Set.Ico_sdiff_left`：Ico_sdiff_left : Ico a b \ {a} = Ioo a b
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Ico_erase_left (a b : α) : (Ico a b).erase a = Ioo a b := by simp [← coe_inj]

@[simp]
/-
**Finset.Ioc_erase_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioc_erase_right (a b : α) : (Ioc a b).erase b = Ioo a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_erase`：coe_erase (a : α) (s : Finset α) : ↑(erase s a) = (s \
 {a} : Set α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Set.Ioc_sdiff_right`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α},
 Set.Ioc b a \ {a} = Set.Ioo b a
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Ioc_erase_right (a b : α) : (Ioc a b).erase b = Ioo a b := by simp [← coe_inj]

@[simp]
/-
**Finset.Icc_sdiff_both** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_sdiff_both (a b : α) : Icc a b \ {a, b} = Ioo a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_sdiff`：coe_sdiff (s₁ s₂ : Finset α) : ↑(s₁ \ s₂) = (s₁ \ s₂ :
 Set α)
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Set.Icc_sdiff_both`：Icc_sdiff_both : Icc a b \ {a, b} = Ioo a b
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Icc_sdiff_both (a b : α) : Icc a b \ {a, b} = Ioo a b := by simp [← coe_inj]

@[deprecated (since := "2026-06-03")] alias Icc_diff_both := Icc_sdiff_both

@[simp]
/-
**Finset.Ico_insert_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_insert_right (h : a <= b) : insert b (Ico a b) = Icc a b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Set.Ico_union_right`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α},
 b ≤ a → Set.Ico b a ∪ {a} = Set.Icc b a
-/
theorem Ico_insert_right (h : a ≤ b) : insert b (Ico a b) = Icc a b := by
  rw [← coe_inj, coe_insert, coe_Icc, coe_Ico, Set.insert_eq, Set.union_comm, Set.Ico_union_right h]

@[simp]
/-
**Finset.Ioc_insert_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioc_insert_left (h : a <= b) : insert a (Ioc a b) = Icc a b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Set.Ioc_union_left`：Ioc_union_left (hab : a <= b) : Ioc a b union {a} = 
Icc a b
-/
theorem Ioc_insert_left (h : a ≤ b) : insert a (Ioc a b) = Icc a b := by
  rw [← coe_inj, coe_insert, coe_Ioc, coe_Icc, Set.insert_eq, Set.union_comm, Set.Ioc_union_left h]

@[simp]
/-
**Finset.Ioo_insert_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioo_insert_left (h : a < b) : insert a (Ioo a b) = Ico a b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Set.Ioo_union_left`：Ioo_union_left (hab : a < b) : Ioo a b union {a} = I
co a b
-/
theorem Ioo_insert_left (h : a < b) : insert a (Ioo a b) = Ico a b := by
  rw [← coe_inj, coe_insert, coe_Ioo, coe_Ico, Set.insert_eq, Set.union_comm, Set.Ioo_union_left h]

@[simp]
/-
**Finset.Ioo_insert_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioo_insert_right (h : a < b) : insert b (Ioo a b) = Ioc a b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Set.Ioo_union_right`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α},
 b < a → Set.Ioo b a ∪ {a} = Set.Ioc b a
-/
theorem Ioo_insert_right (h : a < b) : insert b (Ioo a b) = Ioc a b := by
  rw [← coe_inj, coe_insert, coe_Ioo, coe_Ioc, Set.insert_eq, Set.union_comm, Set.Ioo_union_right h]

@[simp]
/-
**Finset.Icc_sdiff_Ico_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_sdiff_Ico_self (h : a <= b) : Icc a b \ Ico a b = {b}
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_sdiff`：coe_sdiff (s₁ s₂ : Finset α) : ↑(s₁ \ s₂) = (s₁ \ s₂ :
 Set α)
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Set.Icc_sdiff_Ico_same`：Icc_sdiff_Ico_same (h : a <= b) : Icc a b \ Ico 
a b = {b}
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Icc_sdiff_Ico_self (h : a ≤ b) : Icc a b \ Ico a b = {b} := by simp [← coe_inj, h]

@[deprecated (since := "2026-06-03")] alias Icc_diff_Ico_self := Icc_sdiff_Ico_self

@[simp]
/-
**Finset.Icc_sdiff_Ioc_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_sdiff_Ioc_self (h : a <= b) : Icc a b \ Ioc a b = {a}
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_sdiff`：coe_sdiff (s₁ s₂ : Finset α) : ↑(s₁ \ s₂) = (s₁ \ s₂ :
 Set α)
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Set.Icc_sdiff_Ioc_same`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : 
α}, b ≤ a → Set.Icc b a \ Set.Ioc b a = {b}
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Icc_sdiff_Ioc_self (h : a ≤ b) : Icc a b \ Ioc a b = {a} := by simp [← coe_inj, h]

@[deprecated (since := "2026-06-03")] alias Icc_diff_Ioc_self := Icc_sdiff_Ioc_self

@[simp]
/-
**Finset.Icc_sdiff_Ioo_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_sdiff_Ioo_self (h : a <= b) : Icc a b \ Ioo a b = {a, b}
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_sdiff`：coe_sdiff (s₁ s₂ : Finset α) : ↑(s₁ \ s₂) = (s₁ \ s₂ :
 Set α)
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Set.Icc_sdiff_Ioo_same`：Icc_sdiff_Ioo_same (h : a <= b) : Icc a b \ Ioo 
a b = {a, b}
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Icc_sdiff_Ioo_self (h : a ≤ b) : Icc a b \ Ioo a b = {a, b} := by simp [← coe_inj, h]

@[deprecated (since := "2026-06-03")] alias Icc_diff_Ioo_self := Icc_sdiff_Ioo_self

@[simp]
/-
**Finset.Ico_sdiff_Ioo_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_sdiff_Ioo_self (h : a < b) : Ico a b \ Ioo a b = {a}
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_sdiff`：coe_sdiff (s₁ s₂ : Finset α) : ↑(s₁ \ s₂) = (s₁ \ s₂ :
 Set α)
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Set.Ico_sdiff_Ioo_same`：Ico_sdiff_Ioo_same (h : a < b) : Ico a b \ Ioo a
 b = {a}
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Ico_sdiff_Ioo_self (h : a < b) : Ico a b \ Ioo a b = {a} := by simp [← coe_inj, h]

@[deprecated (since := "2026-06-03")] alias Ico_diff_Ioo_self := Ico_sdiff_Ioo_self

@[simp]
/-
**Finset.Ioc_sdiff_Ioo_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioc_sdiff_Ioo_self (h : a < b) : Ioc a b \ Ioo a b = {b}
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_sdiff`：coe_sdiff (s₁ s₂ : Finset α) : ↑(s₁ \ s₂) = (s₁ \ s₂ :
 Set α)
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Set.Ioc_sdiff_Ioo_same`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : 
α}, b < a → Set.Ioc b a \ Set.Ioo b a = {a}
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Ioc_sdiff_Ioo_self (h : a < b) : Ioc a b \ Ioo a b = {b} := by simp [← coe_inj, h]

@[deprecated (since := "2026-06-03")] alias Ioc_diff_Ioo_self := Ioc_sdiff_Ioo_self

@[simp]
/-
**Finset.Ico_inter_Ico_consecutive** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_inter_Ico_consecutive (a b c : α) : Ico a b inter Ico b c = ∅
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `Finset.Ico_disjoint_Ico_consecutive`：Ico_disjoint_Ico_consecutive (a b c
 : α) : Disjoint (Ico a b) (Ico b c)
-/
theorem Ico_inter_Ico_consecutive (a b c : α) : Ico a b ∩ Ico b c = ∅ :=
  (Ico_disjoint_Ico_consecutive a b c).eq_bot

end DecidableEq

-- Those lemmas are purposefully the other way around

/-- `Finset.cons` version of `Finset.Ico_insert_right`. -/
/-
**Finset.Icc_eq_cons_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_eq_cons_Ico (h : a <= b) : Icc a b = (Ico a b).cons b right_notMem_Ico
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.right_notMem_Ico`：right_notMem_Ico : b ∉ Ico a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.Ico_insert_right`：Ico_insert_right (h : a <= b) : insert b (Ico a
 b) = Icc a b

--- 原说明 ---
`Finset.cons` version of `Finset.Ico_insert_right`.
-/
theorem Icc_eq_cons_Ico (h : a ≤ b) : Icc a b = (Ico a b).cons b right_notMem_Ico := by
  classical rw [cons_eq_insert, Ico_insert_right h]

/-- `Finset.cons` version of `Finset.Ioc_insert_left`. -/
/-
**Finset.Icc_eq_cons_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_eq_cons_Ioc (h : a <= b) : Icc a b = (Ioc a b).cons a left_notMem_Ioc
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.left_notMem_Ioc`：left_notMem_Ioc : a ∉ Ioc a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.Ioc_insert_left`：Ioc_insert_left (h : a <= b) : insert a (Ioc a b
) = Icc a b

--- 原说明 ---
`Finset.cons` version of `Finset.Ioc_insert_left`.
-/
theorem Icc_eq_cons_Ioc (h : a ≤ b) : Icc a b = (Ioc a b).cons a left_notMem_Ioc := by
  classical rw [cons_eq_insert, Ioc_insert_left h]

/-- `Finset.cons` version of `Finset.Ioo_insert_right`. -/
/-
**Finset.Ioc_eq_cons_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioc_eq_cons_Ioo (h : a < b) : Ioc a b = (Ioo a b).cons b right_notMem_Ioo
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.right_notMem_Ioo`：right_notMem_Ioo : b ∉ Ioo a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.Ioo_insert_right`：Ioo_insert_right (h : a < b) : insert b (Ioo a 
b) = Ioc a b

--- 原说明 ---
`Finset.cons` version of `Finset.Ioo_insert_right`.
-/
theorem Ioc_eq_cons_Ioo (h : a < b) : Ioc a b = (Ioo a b).cons b right_notMem_Ioo := by
  classical rw [cons_eq_insert, Ioo_insert_right h]

/-- `Finset.cons` version of `Finset.Ioo_insert_left`. -/
/-
**Finset.Ico_eq_cons_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_eq_cons_Ioo (h : a < b) : Ico a b = (Ioo a b).cons a left_notMem_Ioo
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.left_notMem_Ioo`：left_notMem_Ioo : a ∉ Ioo a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.Ioo_insert_left`：Ioo_insert_left (h : a < b) : insert a (Ioo a b)
 = Ico a b

--- 原说明 ---
`Finset.cons` version of `Finset.Ioo_insert_left`.
-/
theorem Ico_eq_cons_Ioo (h : a < b) : Ico a b = (Ioo a b).cons a left_notMem_Ioo := by
  classical rw [cons_eq_insert, Ioo_insert_left h]
/-
**Finset.Ico_filter_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_filter_le_left {a b : α} [DecidablePred (· <= a)] (hab : a < b) : {x i
n Ico a b | x <= a} = {a}
参数：· <= a；hab : a < b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ico_filter_le_left {a b : α} [DecidablePred (· ≤ a)] (hab : a < b) :
    {x ∈ Ico a b | x ≤ a} = {a} := by
  grind
/-
**Finset.card_Ico_eq_card_Icc_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_Ico_eq_card_Icc_sub_one (a b : α) : #(Ico a b) = #(Icc a b) - 1
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.right_notMem_Ico`：right_notMem_Ico : b ∉ Ico a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Icc_eq_cons_Ico`：Icc_eq_cons_Ico (h : a <= b) : Icc a b = (Ico a 
b).cons b right_notMem_Ico
· 使用定理 `Finset.card_cons`：card_cons (h : a ∉ s) : #(s.cons a h) = #s + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_sub_cancel`：∀ (n m : ℕ), n + m - m = n
· 使用定理 `Finset.Ico_eq_empty`：∀ {α : Type u_2} {a b : α} [inst : Preorder α] [ins
t_1 : LocallyFiniteOrder α], ¬a < b → Finset.Ico a b = ∅
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Finset.Icc_eq_empty`：∀ {α : Type u_2} {a b : α} [inst : Preorder α] [ins
t_1 : LocallyFiniteOrder α], ¬a ≤ b → Finset.Icc a b = ∅
· 使用定理 `Finset.card_empty`：card_empty : #(∅ : Finset α) = 0
· 使用定理 `Nat.zero_sub`：∀ (n : ℕ), 0 - n = 0
-/
theorem card_Ico_eq_card_Icc_sub_one (a b : α) : #(Ico a b) = #(Icc a b) - 1 := by
  by_cases h : a ≤ b
  · rw [Icc_eq_cons_Ico h, card_cons]
    exact (Nat.add_sub_cancel _ _).symm
  · rw [Ico_eq_empty fun h' => h h'.le, Icc_eq_empty h, card_empty, Nat.zero_sub]
/-
**Finset.card_Ioc_eq_card_Icc_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_Ioc_eq_card_Icc_sub_one (a b : α) : #(Ioc a b) = #(Icc a b) - 1
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_Ico_eq_card_Icc_sub_one`：card_Ico_eq_card_Icc_sub_one (a b :
 α) : #(Ico a b) = #(Icc a b) - 1
-/
theorem card_Ioc_eq_card_Icc_sub_one (a b : α) : #(Ioc a b) = #(Icc a b) - 1 :=
  @card_Ico_eq_card_Icc_sub_one αᵒᵈ _ _ _ _
/-
**Finset.card_Ioo_eq_card_Ico_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_Ioo_eq_card_Ico_sub_one (a b : α) : #(Ioo a b) = #(Ico a b) - 1
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.left_notMem_Ioo`：left_notMem_Ioo : a ∉ Ioo a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Ico_eq_cons_Ioo`：Ico_eq_cons_Ioo (h : a < b) : Ico a b = (Ioo a b
).cons a left_notMem_Ioo
· 使用定理 `Finset.card_cons`：card_cons (h : a ∉ s) : #(s.cons a h) = #s + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_sub_cancel`：∀ (n m : ℕ), n + m - m = n
· 使用定理 `Finset.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用定理 `Finset.Ico_eq_empty`：∀ {α : Type u_2} {a b : α} [inst : Preorder α] [ins
t_1 : LocallyFiniteOrder α], ¬a < b → Finset.Ico a b = ∅
· 使用定理 `Finset.card_empty`：card_empty : #(∅ : Finset α) = 0
· 使用定理 `Nat.zero_sub`：∀ (n : ℕ), 0 - n = 0
-/
theorem card_Ioo_eq_card_Ico_sub_one (a b : α) : #(Ioo a b) = #(Ico a b) - 1 := by
  by_cases h : a < b
  · rw [Ico_eq_cons_Ioo h, card_cons]
    exact (Nat.add_sub_cancel _ _).symm
  · rw [Ioo_eq_empty h, Ico_eq_empty h, card_empty, Nat.zero_sub]
/-
**Finset.card_Ioo_eq_card_Ioc_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_Ioo_eq_card_Ioc_sub_one (a b : α) : #(Ioo a b) = #(Ioc a b) - 1
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_Ioo_eq_card_Ico_sub_one`：card_Ioo_eq_card_Ico_sub_one (a b :
 α) : #(Ioo a b) = #(Ico a b) - 1
-/
theorem card_Ioo_eq_card_Ioc_sub_one (a b : α) : #(Ioo a b) = #(Ioc a b) - 1 :=
  @card_Ioo_eq_card_Ico_sub_one αᵒᵈ _ _ _ _
/-
**Finset.card_Ioo_eq_card_Icc_sub_two** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_Ioo_eq_card_Icc_sub_two (a b : α) : #(Ioo a b) = #(Icc a b) - 2
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_Ioo_eq_card_Ico_sub_one`：card_Ioo_eq_card_Ico_sub_one (a b :
 α) : #(Ioo a b) = #(Ico a b) - 1
· 使用定理 `Finset.card_Ico_eq_card_Icc_sub_one`：card_Ico_eq_card_Icc_sub_one (a b :
 α) : #(Ico a b) = #(Icc a b) - 1
-/
theorem card_Ioo_eq_card_Icc_sub_two (a b : α) : #(Ioo a b) = #(Icc a b) - 2 := by
  rw [card_Ioo_eq_card_Ico_sub_one, card_Ico_eq_card_Icc_sub_one]
  rfl

end PartialOrder

section Prod

variable {β : Type*}

section sectL

/-
**Finset.uIcc_map_sectL** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：uIcc_map_sectL [Lattice α] [Lattice β] [LocallyFiniteOrder α] [LocallyFini
teOrder β] [DecidableLE (α × β)] (a b : α) (c : β) : (uIcc a b).map (.sectL _ c)
 = uIcc (a, c) (b, c)
参数：α × β；a b : α；c : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.sectL_apply`：∀ (α : Type u_1) {β : Type u_2} (b : β) 
(a : α), (Function.Embedding.sectL α b) a = (a, b)
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
lemma uIcc_map_sectL [Lattice α] [Lattice β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableLE (α × β)] (a b : α) (c : β) :
    (uIcc a b).map (.sectL _ c) = uIcc (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm])

variable [Preorder α] [PartialOrder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
  [DecidableLE (α × β)] (a b : α) (c : β)
/-
**Finset.Icc_map_sectL** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Icc_map_sectL : (Icc a b).map (.sectL _ c) = Icc (a, c) (b, c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.sectL_apply`：∀ (α : Type u_1) {β : Type u_2} (b : β) 
(a : α), (Function.Embedding.sectL α b) a = (a, b)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
lemma Icc_map_sectL : (Icc a b).map (.sectL _ c) = Icc (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm])
/-
**Finset.Ioc_map_sectL** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ioc_map_sectL : (Ioc a b).map (.sectL _ c) = Ioc (a, c) (b, c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.sectL_apply`：∀ (α : Type u_1) {β : Type u_2} (b : β) 
(a : α), (Function.Embedding.sectL α b) a = (a, b)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma Ioc_map_sectL : (Ioc a b).map (.sectL _ c) = Ioc (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm, le_of_lt])
/-
**Finset.Ico_map_sectL** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ico_map_sectL : (Ico a b).map (.sectL _ c) = Ico (a, c) (b, c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.sectL_apply`：∀ (α : Type u_1) {β : Type u_2} (b : β) 
(a : α), (Function.Embedding.sectL α b) a = (a, b)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma Ico_map_sectL : (Ico a b).map (.sectL _ c) = Ico (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm, le_of_lt])
/-
**Finset.Ioo_map_sectL** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ioo_map_sectL : (Ioo a b).map (.sectL _ c) = Ioo (a, c) (b, c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.sectL_apply`：∀ (α : Type u_1) {β : Type u_2} (b : β) 
(a : α), (Function.Embedding.sectL α b) a = (a, b)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma Ioo_map_sectL : (Ioo a b).map (.sectL _ c) = Ioo (a, c) (b, c) := by
  aesop (add safe forward [le_antisymm, le_of_lt])

end sectL

section sectR

/-
**Finset.uIcc_map_sectR** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：uIcc_map_sectR [Lattice α] [Lattice β] [LocallyFiniteOrder α] [LocallyFini
teOrder β] [DecidableLE (α × β)] (c : α) (a b : β) : (uIcc a b).map (.sectR c _)
 = uIcc (c, a) (c, b)
参数：α × β；c : α；a b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.sectR_apply`：∀ {α : Type u_1} (a : α) (β : Type u_2) 
(b : β), (Function.Embedding.sectR a β) b = (a, b)
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
lemma uIcc_map_sectR [Lattice α] [Lattice β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
    [DecidableLE (α × β)] (c : α) (a b : β) :
    (uIcc a b).map (.sectR c _) = uIcc (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm])

variable [PartialOrder α] [Preorder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
  [DecidableLE (α × β)] (c : α) (a b : β)
/-
**Finset.Icc_map_sectR** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Icc_map_sectR : (Icc a b).map (.sectR c _) = Icc (c, a) (c, b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.sectR_apply`：∀ {α : Type u_1} (a : α) (β : Type u_2) 
(b : β), (Function.Embedding.sectR a β) b = (a, b)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
lemma Icc_map_sectR : (Icc a b).map (.sectR c _) = Icc (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm])
/-
**Finset.Ioc_map_sectR** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ioc_map_sectR : (Ioc a b).map (.sectR c _) = Ioc (c, a) (c, b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.sectR_apply`：∀ {α : Type u_1} (a : α) (β : Type u_2) 
(b : β), (Function.Embedding.sectR a β) b = (a, b)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Ioc_map_sectR : (Ioc a b).map (.sectR c _) = Ioc (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm, le_of_lt])
/-
**Finset.Ico_map_sectR** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ico_map_sectR : (Ico a b).map (.sectR c _) = Ico (c, a) (c, b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.sectR_apply`：∀ {α : Type u_1} (a : α) (β : Type u_2) 
(b : β), (Function.Embedding.sectR a β) b = (a, b)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Ico_map_sectR : (Ico a b).map (.sectR c _) = Ico (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm, le_of_lt])
/-
**Finset.Ioo_map_sectR** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：Ioo_map_sectR : (Ioo a b).map (.sectR c _) = Ioo (c, a) (c, b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.sectR_apply`：∀ {α : Type u_1} (a : α) (β : Type u_2) 
(b : β), (Function.Embedding.sectR a β) b = (a, b)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Ioo_map_sectR : (Ioo a b).map (.sectR c _) = Ioo (c, a) (c, b) := by
  aesop (add safe forward [le_antisymm, le_of_lt])

end sectR

end Prod

section BoundedPartialOrder

variable [PartialOrder α]

section OrderTop

variable [LocallyFiniteOrderTop α]

@[simp]
/-
**Finset.Ici_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ici_erase [DecidableEq α] (a : α) : (Ici a).erase a = Ioi a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Ici_erase [DecidableEq α] (a : α) : (Ici a).erase a = Ioi a := by
  ext
  simp_rw [Finset.mem_erase, mem_Ici, mem_Ioi, lt_iff_le_and_ne, and_comm, ne_comm]

@[simp]
/-
**Finset.Ioi_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioi_insert [DecidableEq α] (a : α) : insert a (Ioi a) = Ici a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Ioi_insert [DecidableEq α] (a : α) : insert a (Ioi a) = Ici a := by
  ext
  simp_rw [Finset.mem_insert, mem_Ici, mem_Ioi, le_iff_lt_or_eq, or_comm, eq_comm]
/-
**Finset.notMem_Ioi_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：notMem_Ioi_self {b : α} : b ∉ Ioi b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ioi`：mem_Ioi : x in Ioi a ↔ a < x
-/
theorem notMem_Ioi_self {b : α} : b ∉ Ioi b := fun h => lt_irrefl _ (mem_Ioi.1 h)

-- Purposefully written the other way around
/-- `Finset.cons` version of `Finset.Ioi_insert`. -/
/-
**Finset.Ici_eq_cons_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ici_eq_cons_Ioi (a : α) : Ici a = (Ioi a).cons a notMem_Ioi_self
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.notMem_Ioi_self`：notMem_Ioi_self {b : α} : b ∉ Ioi b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.Ioi_insert`：Ioi_insert [DecidableEq α] (a : α) : insert a (Ioi a)
 = Ici a

--- 原说明 ---
`Finset.cons` version of `Finset.Ioi_insert`.
-/
theorem Ici_eq_cons_Ioi (a : α) : Ici a = (Ioi a).cons a notMem_Ioi_self := by
  classical rw [cons_eq_insert, Ioi_insert]
/-
**Finset.card_Ioi_eq_card_Ici_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_Ioi_eq_card_Ici_sub_one (a : α) : #(Ioi a) = #(Ici a) - 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.notMem_Ioi_self`：notMem_Ioi_self {b : α} : b ∉ Ioi b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Ici_eq_cons_Ioi`：Ici_eq_cons_Ioi (a : α) : Ici a = (Ioi a).cons a
 notMem_Ioi_self
· 使用定理 `Finset.card_cons`：card_cons (h : a ∉ s) : #(s.cons a h) = #s + 1
· 使用定理 `Nat.add_sub_cancel_right`：∀ (n m : ℕ), n + m - m = n
-/
theorem card_Ioi_eq_card_Ici_sub_one (a : α) : #(Ioi a) = #(Ici a) - 1 := by
  rw [Ici_eq_cons_Ioi, card_cons, Nat.add_sub_cancel_right]

end OrderTop

section OrderBot

variable [LocallyFiniteOrderBot α]

@[simp]
/-
**Finset.Iic_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Iic_erase [DecidableEq α] (b : α) : (Iic b).erase b = Iio b
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Iic_erase [DecidableEq α] (b : α) : (Iic b).erase b = Iio b := by
  ext
  simp_rw [Finset.mem_erase, mem_Iic, mem_Iio, lt_iff_le_and_ne, and_comm]

@[simp]
/-
**Finset.Iio_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Iio_insert [DecidableEq α] (b : α) : insert b (Iio b) = Iic b
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Iio_insert [DecidableEq α] (b : α) : insert b (Iio b) = Iic b := by
  ext
  simp_rw [Finset.mem_insert, mem_Iic, mem_Iio, le_iff_lt_or_eq, or_comm]
/-
**Finset.notMem_Iio_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：notMem_Iio_self {b : α} : b ∉ Iio b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iio a ↔ x < a
-/
theorem notMem_Iio_self {b : α} : b ∉ Iio b := fun h => lt_irrefl _ (mem_Iio.1 h)

-- Purposefully written the other way around
/-- `Finset.cons` version of `Finset.Iio_insert`. -/
/-
**Finset.Iic_eq_cons_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Iic_eq_cons_Iio (b : α) : Iic b = (Iio b).cons b notMem_Iio_self
参数：b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.notMem_Iio_self`：notMem_Iio_self {b : α} : b ∉ Iio b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.Iio_insert`：Iio_insert [DecidableEq α] (b : α) : insert b (Iio b)
 = Iic b

--- 原说明 ---
`Finset.cons` version of `Finset.Iio_insert`.
-/
theorem Iic_eq_cons_Iio (b : α) : Iic b = (Iio b).cons b notMem_Iio_self := by
  classical rw [cons_eq_insert, Iio_insert]
/-
**Finset.card_Iio_eq_card_Iic_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_Iio_eq_card_Iic_sub_one (a : α) : #(Iio a) = #(Iic a) - 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.notMem_Iio_self`：notMem_Iio_self {b : α} : b ∉ Iio b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Iic_eq_cons_Iio`：Iic_eq_cons_Iio (b : α) : Iic b = (Iio b).cons b
 notMem_Iio_self
· 使用定理 `Finset.card_cons`：card_cons (h : a ∉ s) : #(s.cons a h) = #s + 1
· 使用定理 `Nat.add_sub_cancel_right`：∀ (n m : ℕ), n + m - m = n
-/
theorem card_Iio_eq_card_Iic_sub_one (a : α) : #(Iio a) = #(Iic a) - 1 := by
  rw [Iic_eq_cons_Iio, card_cons, Nat.add_sub_cancel_right]

end OrderBot

end BoundedPartialOrder

section SemilatticeSup
variable [SemilatticeSup α] [LocallyFiniteOrderBot α]

-- TODO: Why does `id_eq` simplify the LHS here but not the LHS of `Finset.sup_Iic`?
/-
**Finset.sup'_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : SemilatticeSup α] [inst_1 : LocallyFiniteOrderBot
 α] (a : α), (Finset.Iic a).sup' ⋯ id = a
参数：a : α；Finset.Iic a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用引理 `Finset.nonempty_Iic`：nonempty_Iic : (Iic a).Nonempty
· 使用定理 `Finset.sup'_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α
] {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α},   (∀ b ∈ s, f b ≤ a) → s.
sup'…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用定理 `Finset.le_sup'`：le_sup' {b : β} (h : b in s) : f b <= s.sup' ⟨b, h⟩ f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma sup'_Iic (a : α) : (Iic a).sup' nonempty_Iic id = a :=
  le_antisymm (sup'_le _ _ fun _ ↦ mem_Iic.1) <| le_sup' (f := id) <| mem_Iic.2 <| le_refl a
/-
**Finset.sup_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : SemilatticeSup α] [inst_1 : LocallyFiniteOrderBot
 α] [inst_2 : OrderBot α] (a : α),   (Finset.Iic a).sup id = a
参数：a : α；Finset.Iic a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
@[simp] lemma sup_Iic [OrderBot α] (a : α) : (Iic a).sup id = a :=
  le_antisymm (Finset.sup_le fun _ ↦ mem_Iic.1) <| le_sup (f := id) <| mem_Iic.2 <| le_refl a
/-
**Finset.image_subset_Iic_sup** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：image_subset_Iic_sup [OrderBot α] [DecidableEq α] (f : ι -> α) (s : Finset
 ι) : s.image f subseteq Iic (s.sup f)
参数：f : ι -> α；s : Finset ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
lemma image_subset_Iic_sup [OrderBot α] [DecidableEq α] (f : ι → α) (s : Finset ι) :
    s.image f ⊆ Iic (s.sup f) := by
  refine fun i hi ↦ mem_Iic.2 ?_
  obtain ⟨j, hj, rfl⟩ := mem_image.1 hi
  exact le_sup hj
/-
**Finset.subset_Iic_sup_id** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：subset_Iic_sup_id [OrderBot α] (s : Finset α) : s subseteq Iic (s.sup id)
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
lemma subset_Iic_sup_id [OrderBot α] (s : Finset α) : s ⊆ Iic (s.sup id) :=
  fun _ h ↦ mem_Iic.2 <| le_sup (f := id) h

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf α] [LocallyFiniteOrderTop α]

/-
**Finset.inf'_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : SemilatticeInf α] [inst_1 : LocallyFiniteOrderTop
 α] (a : α), (Finset.Ici a).inf' ⋯ id = a
参数：a : α；Finset.Ici a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ge_antisymm`：ge_antisymm : b <= a -> a <= b -> a = b
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用引理 `Finset.nonempty_Ici`：nonempty_Ici : (Ici a).Nonempty
· 使用引理 `Finset.le_inf'`：le_inf'_image₂ {g : γ -> δ} {a : δ} (h : (image₂ f s t).
Nonempty) : a <= inf' (image₂ f s t) h g ↔ forall x in s, forall y in t, a <= g 
(f x…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ici`：mem_Ici : x in Ici a ↔ a <= x
· 使用定理 `Finset.inf'_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf α
] {s : Finset β} (f : β → α) {b : β} (h : b ∈ s),   s.inf' ⋯ f ≤ f b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma inf'_Ici (a : α) : (Ici a).inf' nonempty_Ici id = a :=
  ge_antisymm (le_inf' _ _ fun _ ↦ mem_Ici.1) <| inf'_le (f := id) <| mem_Ici.2 <| le_refl a
/-
**Finset.inf_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : SemilatticeInf α] [inst_1 : LocallyFiniteOrderTop
 α] [inst_2 : OrderTop α] (a : α),   (Finset.Ici a).inf id = a
参数：a : α；Finset.Ici a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Finset.inf_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf α]
 [inst_1 : OrderTop α] {s : Finset β} {f : β → α} {b : β},   b ∈ s → s.inf f ≤ f
 b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Ici`：mem_Ici : x in Ici a ↔ a <= x
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.le_inf`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf α]
 [inst_1 : OrderTop α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, a ≤ f b) 
→ a…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
@[simp] lemma inf_Ici [OrderTop α] (a : α) : (Ici a).inf id = a :=
  le_antisymm (inf_le (f := id) <| mem_Ici.2 <| le_refl a) <| Finset.le_inf fun _ ↦ mem_Ici.1

end SemilatticeInf

section LinearOrder

variable [LinearOrder α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α]

/-
**Finset.Ico_subset_Ico_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_subset_Ico_iff {a₁ b₁ a₂ b₂ : α} (h : a₁ < b₁) : Ico a₁ b₁ subseteq Ic
o a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ <= b₂
参数：h : a₁ < b₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Set.Ico_subset_Ico_iff`：Ico_subset_Ico_iff (h₁ : a₁ < b₁) : Ico a₁ b₁ su
bseteq Ico a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ <= b₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Ico_subset_Ico_iff {a₁ b₁ a₂ b₂ : α} (h : a₁ < b₁) :
    Ico a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ := by
  rw [← coe_subset, coe_Ico, coe_Ico, Set.Ico_subset_Ico_iff h]
/-
**Finset.Ico_union_Ico_eq_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_union_Ico_eq_Ico {a b c : α} (hab : a <= b) (hbc : b <= c) : Ico a b u
nion Ico b c = Ico a c
参数：hab : a <= b；hbc : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Set.Ico_union_Ico_eq_Ico`：Ico_union_Ico_eq_Ico (h₁ : a <= b) (h₂ : b <= 
c) : Ico a b union Ico b c = Ico a c
-/
theorem Ico_union_Ico_eq_Ico {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
    Ico a b ∪ Ico b c = Ico a c := by
  rw [← coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, Set.Ico_union_Ico_eq_Ico hab hbc]

@[simp]
/-
**Finset.Ioc_union_Ioc_eq_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioc_union_Ioc_eq_Ioc {a b c : α} (h₁ : a <= b) (h₂ : b <= c) : Ioc a b uni
on Ioc b c = Ioc a c
参数：h₁ : a <= b；h₂ : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Set.Ioc_union_Ioc_eq_Ioc`：Ioc_union_Ioc_eq_Ioc (h₁ : a <= b) (h₂ : b <= 
c) : Ioc a b union Ioc b c = Ioc a c
-/
theorem Ioc_union_Ioc_eq_Ioc {a b c : α} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    Ioc a b ∪ Ioc b c = Ioc a c := by
  rw [← coe_inj, coe_union, coe_Ioc, coe_Ioc, coe_Ioc, Set.Ioc_union_Ioc_eq_Ioc h₁ h₂]
/-
**Finset.Ico_subset_Ico_union_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_subset_Ico_union_Ico {a b c : α} : Ico a c subseteq Ico a b union Ico 
b c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Set.Ico_subset_Ico_union_Ico`：Ico_subset_Ico_union_Ico : Ico a c subsete
q Ico a b union Ico b c
-/
theorem Ico_subset_Ico_union_Ico {a b c : α} : Ico a c ⊆ Ico a b ∪ Ico b c := by
  rw [← coe_subset, coe_union, coe_Ico, coe_Ico, coe_Ico]
  exact Set.Ico_subset_Ico_union_Ico
/-
**Finset.Ico_union_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_union_Ico {a b c d : α} (h₁ : min a b <= max c d) (h₂ : min c d <= max
 a b) : Ico a b union Ico c d = Ico (min a c) (max b d)
参数：h₁ : min a b <= max c d；h₂ : min c d <= max a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Set.Ico_union_Ico`：Ico_union_Ico (h₁ : min a b <= max c d) (h₂ : min c d
 <= max a b) : Ico a b union Ico c d = Ico (min a c) (max b d)
-/
theorem Ico_union_Ico {a b c d : α} (h₁ : min a b ≤ max c d) (h₂ : min c d ≤ max a b) :
    Ico a b ∪ Ico c d = Ico (min a c) (max b d) := by
  rw [← coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, Set.Ico_union_Ico h₁ h₂]

/-- This is a special case of `Ico_union_Ico` -/
/-
**Finset.Ico_union_Ico'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_union_Ico' {a b c d : α} (hcb : c <= b) (had : a <= d) : Ico a b union
 Ico c d = Ico (min a c) (max b d)
参数：hcb : c <= b；had : a <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Set.Ico_union_Ico'`：Ico_union_Ico' (h₁ : c <= b) (h₂ : a <= d) : Ico a b
 union Ico c d = Ico (min a c) (max b d)

--- 原说明 ---
This is a special case of `Ico_union_Ico`
-/
theorem Ico_union_Ico' {a b c d : α} (hcb : c ≤ b) (had : a ≤ d) :
    Ico a b ∪ Ico c d = Ico (min a c) (max b d) := by
  rw [← coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, Set.Ico_union_Ico' hcb had]
/-
**Finset.Ico_inter_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_inter_Ico {a b c d : α} : Ico a b inter Ico c d = Ico (max a c) (min b
 d)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Finset.coe_inter`：coe_inter (s₁ s₂ : Finset α) : ↑(s₁ inter s₂) = (s₁ in
ter s₂ : Set α)
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Set.Ico_inter_Ico`：Ico_inter_Ico : Ico a₁ b₁ inter Ico a₂ b₂ = Ico (a₁ ⊔
 a₂) (b₁ ⊓ b₂)
-/
theorem Ico_inter_Ico {a b c d : α} : Ico a b ∩ Ico c d = Ico (max a c) (min b d) := by
  rw [← coe_inj, coe_inter, coe_Ico, coe_Ico, coe_Ico, Set.Ico_inter_Ico]
/-
**Finset.Ioc_inter_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioc_inter_Ioc {a b c d : α} : Ioc a b inter Ioc c d = Ioc (max a c) (min b
 d)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioc_inter_Ioc {a b c d : α} : Ioc a b ∩ Ioc c d = Ioc (max a c) (min b d) := by grind

@[simp]
/-
**Finset.Ico_filter_lt** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_filter_lt (a b c : α) : {x in Ico a b | x < c} = Ico a (min b c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ico_filter_lt (a b c : α) : {x ∈ Ico a b | x < c} = Ico a (min b c) := by grind

@[simp]
/-
**Finset.Ico_filter_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_filter_le (a b c : α) : {x in Ico a b | c <= x} = Ico (max a c) b
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ico_filter_le (a b c : α) : {x ∈ Ico a b | c ≤ x} = Ico (max a c) b := by grind

@[simp]
/-
**Finset.Ioo_filter_lt** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioo_filter_lt (a b c : α) : {x in Ioo a b | x < c} = Ioo a (min b c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioo_filter_lt (a b c : α) : {x ∈ Ioo a b | x < c} = Ioo a (min b c) := by grind

@[simp]
/-
**Finset.Iio_filter_lt** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Iio_filter_lt {α} [LinearOrder α] [LocallyFiniteOrderBot α] (a b : α) : {x
 in Iio a | x < b} = Iio (min a b)
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iio_filter_lt {α} [LinearOrder α] [LocallyFiniteOrderBot α] (a b : α) :
    {x ∈ Iio a | x < b} = Iio (min a b) := by grind

@[simp]
/-
**Finset.Ico_sdiff_Ico_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_sdiff_Ico_left (a b c : α) : Ico a b \ Ico a c = Ico (max a c) b
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ico_sdiff_Ico_left (a b c : α) : Ico a b \ Ico a c = Ico (max a c) b := by grind

@[deprecated (since := "2026-06-03")] alias Ico_diff_Ico_left := Ico_sdiff_Ico_left

@[simp]
/-
**Finset.Ico_sdiff_Ico_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ico_sdiff_Ico_right (a b c : α) : Ico a b \ Ico c b = Ico a (min b c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ico_sdiff_Ico_right (a b c : α) : Ico a b \ Ico c b = Ico a (min b c) := by grind

@[deprecated (since := "2026-06-03")] alias Ico_diff_Ico_right := Ico_sdiff_Ico_right

@[simp]
/-
**Finset.Ioc_disjoint_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioc_disjoint_Ioc : Disjoint (Ioc a₁ a₂) (Ioc b₁ b₂) ↔ min a₂ b₂ <= max a₁ 
b₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Ioc_inter_Ioc`：Ioc_inter_Ioc {a b c d : α} : Ioc a b inter Ioc c 
d = Ioc (max a c) (min b d)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Ioc_disjoint_Ioc : Disjoint (Ioc a₁ a₂) (Ioc b₁ b₂) ↔ min a₂ b₂ ≤ max a₁ b₁ := by
  simp_rw [disjoint_iff_inter_eq_empty, Ioc_inter_Ioc, Ioc_eq_empty_iff, not_lt]

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α]

/-
**Finset.Iic_sdiff_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Iic_sdiff_Ioc : Iic b \ Ioc a b = Iic (a ⊓ b)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iic_sdiff_Ioc : Iic b \ Ioc a b = Iic (a ⊓ b) := by
  grind

@[deprecated (since := "2026-06-03")] alias Iic_diff_Ioc := Iic_sdiff_Ioc
/-
**Finset.Iic_sdiff_Ioc_self_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Iic_sdiff_Ioc_self_of_le (hab : a <= b) : Iic b \ Ioc a b = Iic a
参数：hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Iic_sdiff_Ioc`：Iic_sdiff_Ioc : Iic b \ Ioc a b = Iic (a ⊓ b)
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
-/
theorem Iic_sdiff_Ioc_self_of_le (hab : a ≤ b) : Iic b \ Ioc a b = Iic a := by
  rw [Iic_sdiff_Ioc, min_eq_left hab]

@[deprecated (since := "2026-06-03")] alias Iic_diff_Ioc_self_of_le := Iic_sdiff_Ioc_self_of_le
/-
**Finset.Iic_union_Ioc_eq_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Iic_union_Ioc_eq_Iic (h : a <= b) : Iic a union Ioc a b = Iic b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iic_union_Ioc_eq_Iic (h : a ≤ b) : Iic a ∪ Ioc a b = Iic b := by
  grind

end LocallyFiniteOrderBot

end LocallyFiniteOrder

section LocallyFiniteOrderBot
variable [LocallyFiniteOrderBot α] {s : Set α}

/-
**Finset._root_.Set.Infinite.exists_gt** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.Infinite.exists_gt (hs : s.Infinite) : ∀ a, ∃ b ∈ s, a < b :=
  not_bddAbove_iff.1 hs.not_bddAbove
/-
**Finset._root_.Set.infinite_iff_exists_gt** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.infinite_iff_exists_gt [Nonempty α] : s.Infinite ↔ ∀ a, ∃ b ∈ s, a < b :=
  ⟨Set.Infinite.exists_gt, Set.infinite_of_forall_exists_gt⟩

end LocallyFiniteOrderBot

section LocallyFiniteOrderTop
variable [LocallyFiniteOrderTop α] {s : Set α}

/-
**Finset._root_.Set.Infinite.exists_lt** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.Infinite.exists_lt (hs : s.Infinite) : ∀ a, ∃ b ∈ s, b < a :=
  not_bddBelow_iff.1 hs.not_bddBelow
/-
**Finset._root_.Set.infinite_iff_exists_lt** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.infinite_iff_exists_lt [Nonempty α] : s.Infinite ↔ ∀ a, ∃ b ∈ s, b < a :=
  ⟨Set.Infinite.exists_lt, Set.infinite_of_forall_exists_lt⟩

end LocallyFiniteOrderTop

variable [Fintype α] [LocallyFiniteOrderTop α] [LocallyFiniteOrderBot α]

/-
**Finset.Ioi_disjUnion_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Ioi_disjUnion_Iio (a : α) : (Ioi a).disjUnion (Iio a) (disjoint_Ioi_Iio a)
 = ({a} : Finset α)ᶜ
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Finset.disjoint_Ioi_Iio`：disjoint_Ioi_Iio (a : α) : Disjoint (Ioi a) (Ii
o a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.disjUnion_eq_union`：disjUnion_eq_union (s t h) : @disjUnion α s t
 h = s union t
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Ioi_disjUnion_Iio (a : α) :
    (Ioi a).disjUnion (Iio a) (disjoint_Ioi_Iio a) = ({a} : Finset α)ᶜ := by
  ext
  simp [eq_comm]

end LinearOrder

section Lattice

variable [Lattice α] [LocallyFiniteOrder α] {a a₁ a₂ b b₁ b₂ x : α}

/-
**Finset.uIcc_toDual** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：uIcc_toDual (a b : α) : [[toDual a, toDual b]] = [[a, b]].map toDual.toEmb
edding
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.Icc_toDual`：Finset.Icc_toDual : Icc (toDual a) (toDual b) = (Icc 
b a).map toDual.toEmbedding
-/
theorem uIcc_toDual (a b : α) : [[toDual a, toDual b]] = [[a, b]].map toDual.toEmbedding :=
  Icc_toDual (a ⊔ b) (a ⊓ b)

@[simp]
/-
**Finset.uIcc_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.uIcc.eq_1`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : LocallyF
initeOrder α] (a b : α),   Finset.uIcc a b = Finset.Icc (a ⊓ b) (a ⊔ b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
-/
theorem uIcc_of_le (h : a ≤ b) : [[a, b]] = Icc a b := by
  rw [uIcc, inf_eq_left.2 h, sup_eq_right.2 h]

@[simp]
/-
**Finset.uIcc_of_ge** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：uIcc_of_ge (h : b <= a) : [[a, b]] = Icc b a
参数：h : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.uIcc.eq_1`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : LocallyF
initeOrder α] (a b : α),   Finset.uIcc a b = Finset.Icc (a ⊓ b) (a ⊔ b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
-/
theorem uIcc_of_ge (h : b ≤ a) : [[a, b]] = Icc b a := by
  rw [uIcc, inf_eq_right.2 h, sup_eq_left.2 h]
/-
**Finset.uIcc_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：uIcc_comm (a b : α) : [[a, b]] = [[b, a]]
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.uIcc.eq_1`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : LocallyF
initeOrder α] (a b : α),   Finset.uIcc a b = Finset.Icc (a ⊓ b) (a ⊔ b)
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
-/
theorem uIcc_comm (a b : α) : [[a, b]] = [[b, a]] := by
  rw [uIcc, uIcc, inf_comm, sup_comm]
/-
**Finset.uIcc_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：uIcc_self : [[a, a]] = {a}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Finset.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem uIcc_self : [[a, a]] = {a} := by simp [uIcc]

@[simp]
/-
**Finset.nonempty_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：nonempty_uIcc : Finset.Nonempty [[a, b]]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.nonempty_Icc`：nonempty_Icc : (Icc a b).Nonempty ↔ a <= b
· 使用定理 `inf_le_sup`：inf_le_sup : a ⊓ b <= a ⊔ b
-/
theorem nonempty_uIcc : Finset.Nonempty [[a, b]] :=
  nonempty_Icc.2 inf_le_sup
/-
**Finset.Icc_subset_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_subset_uIcc : Icc a b subseteq [[a, b]]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Icc_subset_Icc`：Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : 
Icc a₁ b₁ subseteq Icc a₂ b₂
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem Icc_subset_uIcc : Icc a b ⊆ [[a, b]] :=
  Icc_subset_Icc inf_le_left le_sup_right
/-
**Finset.Icc_subset_uIcc'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_subset_uIcc' : Icc b a subseteq [[a, b]]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Icc_subset_Icc`：Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : 
Icc a₁ b₁ subseteq Icc a₂ b₂
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem Icc_subset_uIcc' : Icc b a ⊆ [[a, b]] :=
  Icc_subset_Icc inf_le_right le_sup_left
/-
**Finset.left_mem_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：left_mem_uIcc : a in [[a, b]]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Icc`：mem_Icc : x in Icc a b ↔ a <= x ∧ x <= b
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem left_mem_uIcc : a ∈ [[a, b]] :=
  mem_Icc.2 ⟨inf_le_left, le_sup_left⟩
/-
**Finset.right_mem_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：right_mem_uIcc : b in [[a, b]]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Icc`：mem_Icc : x in Icc a b ↔ a <= x ∧ x <= b
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem right_mem_uIcc : b ∈ [[a, b]] :=
  mem_Icc.2 ⟨inf_le_right, le_sup_right⟩
/-
**Finset.mem_uIcc_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_uIcc_of_le (ha : a <= x) (hb : x <= b) : x in [[a, b]]
参数：ha : a <= x；hb : x <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Icc_subset_uIcc`：Icc_subset_uIcc : Icc a b subseteq [[a, b]]
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Icc`：mem_Icc : x in Icc a b ↔ a <= x ∧ x <= b
-/
theorem mem_uIcc_of_le (ha : a ≤ x) (hb : x ≤ b) : x ∈ [[a, b]] :=
  Icc_subset_uIcc <| mem_Icc.2 ⟨ha, hb⟩
/-
**Finset.mem_uIcc_of_ge** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_uIcc_of_ge (hb : b <= x) (ha : x <= a) : x in [[a, b]]
参数：hb : b <= x；ha : x <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Icc_subset_uIcc'`：Icc_subset_uIcc' : Icc b a subseteq [[a, b]]
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Icc`：mem_Icc : x in Icc a b ↔ a <= x ∧ x <= b
-/
theorem mem_uIcc_of_ge (hb : b ≤ x) (ha : x ≤ a) : x ∈ [[a, b]] :=
  Icc_subset_uIcc' <| mem_Icc.2 ⟨hb, ha⟩
/-
**Finset.uIcc_subset_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：uIcc_subset_uIcc (h₁ : a₁ in [[a₂, b₂]]) (h₂ : b₁ in [[a₂, b₂]]) : [[a₁, b
₁]] subseteq [[a₂, b₂]]
参数：h₁ : a₁ in [[a₂, b₂]]；h₂ : b₁ in [[a₂, b₂]]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Icc_subset_Icc`：Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : 
Icc a₁ b₁ subseteq Icc a₂ b₂
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_uIcc`：mem_uIcc : x in uIcc a b ↔ a ⊓ b <= x ∧ x <= a ⊔ b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem uIcc_subset_uIcc (h₁ : a₁ ∈ [[a₂, b₂]]) (h₂ : b₁ ∈ [[a₂, b₂]]) :
    [[a₁, b₁]] ⊆ [[a₂, b₂]] := by
  rw [mem_uIcc] at h₁ h₂
  exact Icc_subset_Icc (_root_.le_inf h₁.1 h₂.1) (_root_.sup_le h₁.2 h₂.2)
/-
**Finset.uIcc_subset_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：uIcc_subset_Icc (ha : a₁ in Icc a₂ b₂) (hb : b₁ in Icc a₂ b₂) : [[a₁, b₁]]
 subseteq Icc a₂ b₂
参数：ha : a₁ in Icc a₂ b₂；hb : b₁ in Icc a₂ b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Icc_subset_Icc`：Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : 
Icc a₁ b₁ subseteq Icc a₂ b₂
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_Icc`：mem_Icc : x in Icc a b ↔ a <= x ∧ x <= b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem uIcc_subset_Icc (ha : a₁ ∈ Icc a₂ b₂) (hb : b₁ ∈ Icc a₂ b₂) : [[a₁, b₁]] ⊆ Icc a₂ b₂ := by
  rw [mem_Icc] at ha hb
  exact Icc_subset_Icc (_root_.le_inf ha.1 hb.1) (_root_.sup_le ha.2 hb.2)
/-
**Finset.uIcc_subset_uIcc_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：uIcc_subset_uIcc_iff_mem : [[a₁, b₁]] subseteq [[a₂, b₂]] ↔ a₁ in [[a₂, b₂
]] ∧ b₁ in [[a₂, b₂]]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.left_mem_uIcc`：left_mem_uIcc : a in [[a, b]]
· 使用定理 `Finset.right_mem_uIcc`：right_mem_uIcc : b in [[a, b]]
· 使用定理 `Finset.uIcc_subset_uIcc`：uIcc_subset_uIcc (h₁ : a₁ in [[a₂, b₂]]) (h₂ : 
b₁ in [[a₂, b₂]]) : [[a₁, b₁]] subseteq [[a₂, b₂]]
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem uIcc_subset_uIcc_iff_mem : [[a₁, b₁]] ⊆ [[a₂, b₂]] ↔ a₁ ∈ [[a₂, b₂]] ∧ b₁ ∈ [[a₂, b₂]] :=
  ⟨fun h => ⟨h left_mem_uIcc, h right_mem_uIcc⟩, fun h => uIcc_subset_uIcc h.1 h.2⟩
/-
**Finset.uIcc_subset_uIcc_iff_le'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：uIcc_subset_uIcc_iff_le' : [[a₁, b₁]] subseteq [[a₂, b₂]] ↔ a₂ ⊓ b₂ <= a₁ 
⊓ b₁ ∧ a₁ ⊔ b₁ <= a₂ ⊔ b₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Icc_subset_Icc_iff`：Icc_subset_Icc_iff (h₁ : a₁ <= b₁) : Icc a₁ b
₁ subseteq Icc a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ <= b₂
· 使用定理 `inf_le_sup`：inf_le_sup : a ⊓ b <= a ⊔ b
-/
theorem uIcc_subset_uIcc_iff_le' :
    [[a₁, b₁]] ⊆ [[a₂, b₂]] ↔ a₂ ⊓ b₂ ≤ a₁ ⊓ b₁ ∧ a₁ ⊔ b₁ ≤ a₂ ⊔ b₂ :=
  Icc_subset_Icc_iff inf_le_sup
/-
**Finset.uIcc_subset_uIcc_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：uIcc_subset_uIcc_right (h : x in [[a, b]]) : [[x, b]] subseteq [[a, b]]
参数：h : x in [[a, b]]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.uIcc_subset_uIcc`：uIcc_subset_uIcc (h₁ : a₁ in [[a₂, b₂]]) (h₂ : 
b₁ in [[a₂, b₂]]) : [[a₁, b₁]] subseteq [[a₂, b₂]]
· 使用定理 `Finset.right_mem_uIcc`：right_mem_uIcc : b in [[a, b]]
-/
theorem uIcc_subset_uIcc_right (h : x ∈ [[a, b]]) : [[x, b]] ⊆ [[a, b]] :=
  uIcc_subset_uIcc h right_mem_uIcc
/-
**Finset.uIcc_subset_uIcc_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：uIcc_subset_uIcc_left (h : x in [[a, b]]) : [[a, x]] subseteq [[a, b]]
参数：h : x in [[a, b]]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.uIcc_subset_uIcc`：uIcc_subset_uIcc (h₁ : a₁ in [[a₂, b₂]]) (h₂ : 
b₁ in [[a₂, b₂]]) : [[a₁, b₁]] subseteq [[a₂, b₂]]
· 使用定理 `Finset.left_mem_uIcc`：left_mem_uIcc : a in [[a, b]]
-/
theorem uIcc_subset_uIcc_left (h : x ∈ [[a, b]]) : [[a, x]] ⊆ [[a, b]] :=
  uIcc_subset_uIcc left_mem_uIcc h

end Lattice

section DistribLattice

variable [DistribLattice α] [LocallyFiniteOrder α] {a b c : α}

/-
**Finset.eq_of_mem_uIcc_of_mem_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_of_mem_uIcc_of_mem_uIcc : a in [[b, c]] -> b in [[a, c]] -> a = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Set.eq_of_mem_uIcc_of_mem_uIcc`：eq_of_mem_uIcc_of_mem_uIcc (ha : a in [[
b, c]]) (hb : b in [[a, c]]) : a = b
-/
theorem eq_of_mem_uIcc_of_mem_uIcc : a ∈ [[b, c]] → b ∈ [[a, c]] → a = b := by
  simp_rw [mem_uIcc]
  exact Set.eq_of_mem_uIcc_of_mem_uIcc
/-
**Finset.eq_of_mem_uIcc_of_mem_uIcc'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_of_mem_uIcc_of_mem_uIcc' : b in [[a, c]] -> c in [[a, b]] -> b = c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Set.eq_of_mem_uIcc_of_mem_uIcc'`：eq_of_mem_uIcc_of_mem_uIcc' : b in [[a,
 c]] -> c in [[a, b]] -> b = c
-/
theorem eq_of_mem_uIcc_of_mem_uIcc' : b ∈ [[a, c]] → c ∈ [[a, b]] → b = c := by
  simp_rw [mem_uIcc]
  exact Set.eq_of_mem_uIcc_of_mem_uIcc'
/-
**Finset.uIcc_injective_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：uIcc_injective_right (a : α) : Injective fun b => [[b, a]]
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_mem_uIcc_of_mem_uIcc`：eq_of_mem_uIcc_of_mem_uIcc : a in [[b
, c]] -> b in [[a, c]] -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.ext_iff`：∀ {α : Type u_1} {s₁ s₂ : Finset α}, s₁ = s₂ ↔ ∀ (a : α)
, a ∈ s₁ ↔ a ∈ s₂
· 使用定理 `Finset.left_mem_uIcc`：left_mem_uIcc : a in [[a, b]]
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem uIcc_injective_right (a : α) : Injective fun b => [[b, a]] := fun b c h => by
  rw [Finset.ext_iff] at h
  exact eq_of_mem_uIcc_of_mem_uIcc ((h _).1 left_mem_uIcc) ((h _).2 left_mem_uIcc)
/-
**Finset.uIcc_injective_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：uIcc_injective_left (a : α) : Injective (uIcc a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.uIcc_comm`：uIcc_comm (a b : α) : [[a, b]] = [[b, a]]
· 使用定理 `Finset.uIcc_injective_right`：uIcc_injective_right (a : α) : Injective fu
n b => [[b, a]]
-/
theorem uIcc_injective_left (a : α) : Injective (uIcc a) := by
  simpa only [uIcc_comm] using uIcc_injective_right a

end DistribLattice

section LinearOrder

variable [LinearOrder α] [LocallyFiniteOrder α] {a a₁ a₂ b b₁ b₂ c : α}

/-
**Finset.Icc_min_max** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：Icc_min_max : Icc (min a b) (max a b) = [[a, b]]
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Icc_min_max : Icc (min a b) (max a b) = [[a, b]] :=
  rfl
/-
**Finset.uIcc_of_not_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：uIcc_of_not_le (h : ¬a <= b) : [[a, b]] = Icc b a
参数：h : ¬a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.uIcc_of_ge`：uIcc_of_ge (h : b <= a) : [[a, b]] = Icc b a
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
-/
theorem uIcc_of_not_le (h : ¬a ≤ b) : [[a, b]] = Icc b a :=
  uIcc_of_ge <| le_of_not_ge h
/-
**Finset.uIcc_of_not_ge** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：uIcc_of_not_ge (h : ¬b <= a) : [[a, b]] = Icc a b
参数：h : ¬b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
-/
theorem uIcc_of_not_ge (h : ¬b ≤ a) : [[a, b]] = Icc a b :=
  uIcc_of_le <| le_of_not_ge h
/-
**Finset.uIcc_eq_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：uIcc_eq_union : [[a, b]] = Icc a b union Icc b a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_uIcc`：coe_uIcc (a b : α) : (Finset.uIcc a b : Set α) = Set.uI
cc a b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用引理 `Set.uIcc_eq_union`：uIcc_eq_union : [[a, b]] = Icc a b union Icc b a
-/
theorem uIcc_eq_union : [[a, b]] = Icc a b ∪ Icc b a :=
  coe_injective <| by
    push_cast
    exact Set.uIcc_eq_union
/-
**Finset.mem_uIcc'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_uIcc' : a in [[b, c]] ↔ b <= a ∧ a <= c ∨ c <= a ∧ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.uIcc_eq_union`：uIcc_eq_union : [[a, b]] = Icc a b union Icc b a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_uIcc' : a ∈ [[b, c]] ↔ b ≤ a ∧ a ≤ c ∨ c ≤ a ∧ a ≤ b := by simp [uIcc_eq_union]
/-
**Finset.notMem_uIcc_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：notMem_uIcc_of_lt : c < a -> c < b -> c ∉ [[a, b]]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_uIcc`：mem_uIcc : x in uIcc a b ↔ a ⊓ b <= x ∧ x <= a ⊔ b
· 使用引理 `Set.notMem_uIcc_of_lt`：notMem_uIcc_of_lt (ha : c < a) (hb : c < b) : c ∉
 [[a, b]]
-/
theorem notMem_uIcc_of_lt : c < a → c < b → c ∉ [[a, b]] := by
  rw [mem_uIcc]
  exact Set.notMem_uIcc_of_lt
/-
**Finset.notMem_uIcc_of_gt** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：notMem_uIcc_of_gt : a < c -> b < c -> c ∉ [[a, b]]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_uIcc`：mem_uIcc : x in uIcc a b ↔ a ⊓ b <= x ∧ x <= a ⊔ b
· 使用引理 `Set.notMem_uIcc_of_gt`：notMem_uIcc_of_gt (ha : a < c) (hb : b < c) : c ∉
 [[a, b]]
-/
theorem notMem_uIcc_of_gt : a < c → b < c → c ∉ [[a, b]] := by
  rw [mem_uIcc]
  exact Set.notMem_uIcc_of_gt
/-
**Finset.uIcc_subset_uIcc_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：uIcc_subset_uIcc_iff_le : [[a₁, b₁]] subseteq [[a₂, b₂]] ↔ min a₂ b₂ <= mi
n a₁ b₁ ∧ max a₁ b₁ <= max a₂ b₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.uIcc_subset_uIcc_iff_le'`：uIcc_subset_uIcc_iff_le' : [[a₁, b₁]] s
ubseteq [[a₂, b₂]] ↔ a₂ ⊓ b₂ <= a₁ ⊓ b₁ ∧ a₁ ⊔ b₁ <= a₂ ⊔ b₂
-/
theorem uIcc_subset_uIcc_iff_le :
    [[a₁, b₁]] ⊆ [[a₂, b₂]] ↔ min a₂ b₂ ≤ min a₁ b₁ ∧ max a₁ b₁ ≤ max a₂ b₂ :=
  uIcc_subset_uIcc_iff_le'

/-- A sort of triangle inequality. -/
/-
**Finset.uIcc_subset_uIcc_union_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：uIcc_subset_uIcc_union_uIcc : [[a, c]] subseteq [[a, b]] union [[b, c]]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_uIcc`：coe_uIcc (a b : α) : (Finset.uIcc a b : Set α) = Set.uI
cc a b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用引理 `Set.uIcc_subset_uIcc_union_uIcc`：uIcc_subset_uIcc_union_uIcc : [[a, c]] 
subseteq [[a, b]] union [[b, c]]

--- 原说明 ---
A sort of triangle inequality.
-/
theorem uIcc_subset_uIcc_union_uIcc : [[a, c]] ⊆ [[a, b]] ∪ [[b, c]] :=
  coe_subset.1 <| by
    push_cast
    exact Set.uIcc_subset_uIcc_union_uIcc

end LinearOrder
end Finset

/-! ### `⩿`, `⋖` and monotonicity -/

section Cover

open Finset Relation

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-
**transGen_wcovBy_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：transGen_wcovBy_of_le [Preorder α] [LocallyFiniteOrder α] {x y : α} (hxy :
 x <= y) : TransGen (· ⩿ ·) x y
参数：hxy : x <= y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `transGen_wcovBy_of_le._unary`：∀ {α : Type u_2} [inst : Preorder α] [Loca
llyFiniteOrder α] {x : α} (_x : (y : α) ×' x ≤ y),   Relation.TransGen (fun x1 x
2 => x1 ⩿ x2) x _x…
-/
lemma transGen_wcovBy_of_le [Preorder α] [LocallyFiniteOrder α] {x y : α} (hxy : x ≤ y) :
    TransGen (· ⩿ ·) x y := by
  -- We proceed by well-founded induction on the cardinality of `Icc x y`.
  -- It's impossible for the cardinality to be zero since `x ≤ y`
  have : #(Ico x y) < #(Icc x y) := card_lt_card <|
    ⟨Ico_subset_Icc_self, not_subset.mpr ⟨y, ⟨right_mem_Icc.mpr hxy, right_notMem_Ico⟩⟩⟩
  by_cases hxy' : y ≤ x
  -- If `y ≤ x`, then `x ⩿ y`
  · exact .single <| wcovBy_of_le_of_le hxy hxy'
  /- and if `¬ y ≤ x`, then `x < y`, not because it is a linear order, but because `x ≤ y`
  already. In that case, since `z` is maximal in `Ico x y`, then `z ⩿ y` and we can use the
  induction hypothesis to show that `Relation.TransGen (· ⩿ ·) x z`. -/
  · obtain ⟨z, hxz, hz⟩ :=
      (Set.finite_Ico x y).exists_le_maximal <| Set.left_mem_Ico.2 <| hxy.lt_of_not_ge hxy'
    have z_card := calc
      #(Icc x z) ≤ #(Ico x y) := card_le_card <| Icc_subset_Ico_right hz.1.2
      _          < #(Icc x y) := this
    have h₁ := transGen_wcovBy_of_le hz.1.1
    have h₂ : z ⩿ y :=
      ⟨hz.1.2.le, fun c hzc hcy ↦ hzc.not_ge <| hz.2 ⟨hz.1.1.trans hzc.le, hcy⟩ hzc.le⟩
    exact .tail h₁ h₂
termination_by #(Icc x y)

/-- In a locally finite preorder, `≤` is the transitive closure of `⩿`. -/
/-
**le_iff_transGen_wcovBy** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_iff_transGen_wcovBy [Preorder α] [LocallyFiniteOrder α] {x y : α} : x <
= y ↔ TransGen (· ⩿ ·) x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `transGen_wcovBy_of_le`：transGen_wcovBy_of_le [Preorder α] [LocallyFinite
Order α] {x y : α} (hxy : x <= y) : TransGen (· ⩿ ·) x y
· 使用定理 `WCovBy.le`：WCovBy.le (h : a ⩿ b) : a <= b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c

--- 原说明 ---
In a locally finite preorder, `≤` is the transitive closure of `⩿`.
-/
lemma le_iff_transGen_wcovBy [Preorder α] [LocallyFiniteOrder α] {x y : α} :
    x ≤ y ↔ TransGen (· ⩿ ·) x y := by
  refine ⟨transGen_wcovBy_of_le, fun h ↦ ?_⟩
  induction h with
  | single h => exact h.le
  | tail _ h₁ h₂ => exact h₂.trans h₁.le

/-- In a locally finite partial order, `≤` is the reflexive transitive closure of `⋖`. -/
/-
**le_iff_reflTransGen_covBy** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_iff_reflTransGen_covBy [PartialOrder α] [LocallyFiniteOrder α] {x y : α
} : x <= y ↔ ReflTransGen (· ⋖ ·) x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_iff_transGen_wcovBy`：le_iff_transGen_wcovBy [Preorder α] [LocallyFini
teOrder α] {x y : α} : x <= y ↔ TransGen (· ⩿ ·) x y
· 使用引理 `wcovBy_eq_reflGen_covBy`：wcovBy_eq_reflGen_covBy [PartialOrder α] : (· ⩿
 · : α -> α -> Prop) = ReflGen (· ⋖ ·)
· 使用定理 `Relation.transGen_reflGen`：∀ {α : Type u_1} {r : α → α → Prop}, Relation
.TransGen (Relation.ReflGen r) = Relation.ReflTransGen r
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
In a locally finite partial order, `≤` is the reflexive transitive closure of `⋖
`.
-/
lemma le_iff_reflTransGen_covBy [PartialOrder α] [LocallyFiniteOrder α] {x y : α} :
    x ≤ y ↔ ReflTransGen (· ⋖ ·) x y := by
  rw [le_iff_transGen_wcovBy, wcovBy_eq_reflGen_covBy, transGen_reflGen]
/-
**transGen_covBy_of_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：transGen_covBy_of_lt [Preorder α] [LocallyFiniteOrder α] {x y : α} (hxy : 
x < y) : TransGen (· ⋖ ·) x y
参数：hxy : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `transGen_covBy_of_lt._unary`：∀ {α : Type u_2} [inst : Preorder α] [Local
lyFiniteOrder α] {x : α} (_x : (y : α) ×' x < y),   Relation.TransGen (fun x1 x2
 => x1 ⋖ x2) x _x…
-/
lemma transGen_covBy_of_lt [Preorder α] [LocallyFiniteOrder α] {x y : α} (hxy : x < y) :
    TransGen (· ⋖ ·) x y := by
  -- We proceed by well-founded induction on the cardinality of `Ico x y`.
  -- It's impossible for the cardinality to be zero since `x < y`
  -- `Ico x y` is a nonempty finset and so contains a maximal element `z` and
  -- `Ico x z` has cardinality strictly less than the cardinality of `Ico x y`
  obtain ⟨z, hxz, hz⟩ := (Set.finite_Ico x y).exists_le_maximal <| Set.left_mem_Ico.2 hxy
  have z_card : #(Ico x z) < #(Ico x y) := card_lt_card <| ssubset_iff_of_subset
    (Ico_subset_Ico_right hz.1.2.le) |>.mpr ⟨z, mem_Ico.2 hz.1, right_notMem_Ico⟩
  /- Since `z` is maximal in `Ico x y`, `z ⋖ y`. -/
  have hzy : z ⋖ y :=
    ⟨hz.1.2, fun c hc hcy ↦ hc.not_ge <| hz.2 (⟨(hz.1.1.trans_lt hc).le, hcy⟩) hc.le⟩
  by_cases hxz : x < z
  /- when `x < z`, then we may use the induction hypothesis to get a chain
  `Relation.TransGen (· ⋖ ·) x z`, which we can extend with `Relation.TransGen.tail`. -/
  · exact .tail (transGen_covBy_of_lt hxz) hzy
  /- when `¬ x < z`, then actually `z ≤ x` (not because it's a linear order, but because
  `x ≤ z`), and since `z ⋖ y` we conclude that `x ⋖ y`, then `Relation.TransGen.single`. -/
  · simp only [lt_iff_le_not_ge, not_and, not_not] at hxz
    exact .single (hzy.of_le_of_lt (hxz hz.1.1) hxy)
termination_by #(Ico x y)

/-- In a locally finite preorder, `<` is the transitive closure of `⋖`. -/
/-
**lt_iff_transGen_covBy** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_iff_transGen_covBy [Preorder α] [LocallyFiniteOrder α] {x y : α} : x < 
y ↔ TransGen (· ⋖ ·) x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `transGen_covBy_of_lt`：transGen_covBy_of_lt [Preorder α] [LocallyFiniteOr
der α] {x y : α} (hxy : x < y) : TransGen (· ⋖ ·) x y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c

--- 原说明 ---
In a locally finite preorder, `<` is the transitive closure of `⋖`.
-/
lemma lt_iff_transGen_covBy [Preorder α] [LocallyFiniteOrder α] {x y : α} :
    x < y ↔ TransGen (· ⋖ ·) x y := by
  refine ⟨transGen_covBy_of_lt, fun h ↦ ?_⟩
  induction h with
  | single hx => exact hx.1
  | tail _ hb ih => exact ih.trans hb.1

variable {β : Type*}

/-- A function from a locally finite preorder is monotone if and only if it is monotone when
restricted to pairs satisfying `a ⩿ b`. -/
/-
**monotone_iff_forall_wcovBy** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monotone_iff_forall_wcovBy [Preorder α] [LocallyFiniteOrder α] [Preorder β
] (f : α -> β) : Monotone f ↔ forall a b : α, a ⩿ b -> f a <= f b
参数：f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WCovBy.le`：WCovBy.le (h : a ⩿ b) : a <= b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Relation.transGen_eq_self`：transGen_eq_self [IsTrans α r] : TransGen r =
 r
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Relation.TransGen.lift`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pro
p} {p : β → β → Prop} (f : α → β),   r ≤ Function.onFun p f → Relation.TransGen 
r ≤ Function…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_iff_transGen_wcovBy`：le_iff_transGen_wcovBy [Preorder α] [LocallyFini
teOrder α] {x y : α} : x <= y ↔ TransGen (· ⩿ ·) x y

--- 原说明 ---
A function from a locally finite preorder is monotone if and only if it is monot
one when
restricted to pairs satisfying `a ⩿ b`.
-/
lemma monotone_iff_forall_wcovBy [Preorder α] [LocallyFiniteOrder α] [Preorder β]
    (f : α → β) : Monotone f ↔ ∀ a b : α, a ⩿ b → f a ≤ f b := by
  refine ⟨fun hf _ _ h ↦ hf h.le, fun h a b hab ↦ ?_⟩
  simpa [transGen_eq_self] using TransGen.lift f h a b <| le_iff_transGen_wcovBy.mp hab

/-- A function from a locally finite partial order is monotone if and only if it is monotone when
restricted to pairs satisfying `a ⋖ b`. -/
/-
**monotone_iff_forall_covBy** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monotone_iff_forall_covBy [PartialOrder α] [LocallyFiniteOrder α] [Preorde
r β] (f : α -> β) : Monotone f ↔ forall a b : α, a ⋖ b -> f a <= f b
参数：f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovBy.le`：CovBy.le (h : a ⋖ b) : a <= b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Relation.reflTransGen_eq_self`：reflTransGen_eq_self [Std.Refl r] [IsTran
s α r] : ReflTransGen r = r
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Relation.ReflTransGen.lift`：∀ {α : Type u_1} {β : Type u_2} {r : α → α →
 Prop} {p : β → β → Prop} (f : α → β),   r ≤ Function.onFun p f → Relation.ReflT
ransGen r ≤ Func…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_iff_reflTransGen_covBy`：le_iff_reflTransGen_covBy [PartialOrder α] [L
ocallyFiniteOrder α] {x y : α} : x <= y ↔ ReflTransGen (· ⋖ ·) x y

--- 原说明 ---
A function from a locally finite partial order is monotone if and only if it is 
monotone when
restricted to pairs satisfying `a ⋖ b`.
-/
lemma monotone_iff_forall_covBy [PartialOrder α] [LocallyFiniteOrder α] [Preorder β]
    (f : α → β) : Monotone f ↔ ∀ a b : α, a ⋖ b → f a ≤ f b := by
  refine ⟨fun hf _ _ h ↦ hf h.le, fun h a b hab ↦ ?_⟩
  simpa [reflTransGen_eq_self] using ReflTransGen.lift f h a b <| le_iff_reflTransGen_covBy.mp hab

/-- A function from a locally finite preorder is strictly monotone if and only if it is strictly
monotone when restricted to pairs satisfying `a ⋖ b`. -/
/-
**strictMono_iff_forall_covBy** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictMono_iff_forall_covBy [Preorder α] [LocallyFiniteOrder α] [Preorder 
β] (f : α -> β) : StrictMono f ↔ forall a b : α, a ⋖ b -> f a < f b
参数：f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
· 使用定理 `Relation.TransGen.lift`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pro
p} {p : β → β → Prop} (f : α → β),   r ≤ Function.onFun p f → Relation.TransGen 
r ≤ Function…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Relation.transGen_eq_self`：transGen_eq_self [IsTrans α r] : TransGen r =
 r
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `lt_iff_transGen_covBy`：lt_iff_transGen_covBy [Preorder α] [LocallyFinite
Order α] {x y : α} : x < y ↔ TransGen (· ⋖ ·) x y

--- 原说明 ---
A function from a locally finite preorder is strictly monotone if and only if it
 is strictly
monotone when restricted to pairs satisfying `a ⋖ b`.
-/
lemma strictMono_iff_forall_covBy [Preorder α] [LocallyFiniteOrder α] [Preorder β]
    (f : α → β) : StrictMono f ↔ ∀ a b : α, a ⋖ b → f a < f b := by
  refine ⟨fun hf _ _ h ↦ hf h.lt, fun h a b hab ↦ ?_⟩
  have := Relation.TransGen.lift f h a b
  rw [← lt_iff_transGen_covBy, transGen_eq_self] at this
  exact this hab

/-- A function from a locally finite preorder is antitone if and only if it is antitone when
restricted to pairs satisfying `a ⩿ b`. -/
/-
**antitone_iff_forall_wcovBy** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antitone_iff_forall_wcovBy [Preorder α] [LocallyFiniteOrder α] [Preorder β
] (f : α -> β) : Antitone f ↔ forall a b : α, a ⩿ b -> f b <= f a
参数：f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `monotone_iff_forall_wcovBy`：monotone_iff_forall_wcovBy [Preorder α] [Loc
allyFiniteOrder α] [Preorder β] (f : α -> β) : Monotone f ↔ forall a b : α, a ⩿ 
b -> f a <= f b

--- 原说明 ---
A function from a locally finite preorder is antitone if and only if it is antit
one when
restricted to pairs satisfying `a ⩿ b`.
-/
lemma antitone_iff_forall_wcovBy [Preorder α] [LocallyFiniteOrder α] [Preorder β]
    (f : α → β) : Antitone f ↔ ∀ a b : α, a ⩿ b → f b ≤ f a :=
  monotone_iff_forall_wcovBy (β := βᵒᵈ) f

/-- A function from a locally finite partial order is antitone if and only if it is antitone when
restricted to pairs satisfying `a ⋖ b`. -/
/-
**antitone_iff_forall_covBy** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antitone_iff_forall_covBy [PartialOrder α] [LocallyFiniteOrder α] [Preorde
r β] (f : α -> β) : Antitone f ↔ forall a b : α, a ⋖ b -> f b <= f a
参数：f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `monotone_iff_forall_covBy`：monotone_iff_forall_covBy [PartialOrder α] [L
ocallyFiniteOrder α] [Preorder β] (f : α -> β) : Monotone f ↔ forall a b : α, a 
⋖ b -> f a <= f…

--- 原说明 ---
A function from a locally finite partial order is antitone if and only if it is 
antitone when
restricted to pairs satisfying `a ⋖ b`.
-/
lemma antitone_iff_forall_covBy [PartialOrder α] [LocallyFiniteOrder α] [Preorder β]
    (f : α → β) : Antitone f ↔ ∀ a b : α, a ⋖ b → f b ≤ f a :=
  monotone_iff_forall_covBy (β := βᵒᵈ) f

/-- A function from a locally finite preorder is strictly antitone if and only if it is strictly
antitone when restricted to pairs satisfying `a ⋖ b`. -/
/-
**strictAnti_iff_forall_covBy** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictAnti_iff_forall_covBy [Preorder α] [LocallyFiniteOrder α] [Preorder 
β] (f : α -> β) : StrictAnti f ↔ forall a b : α, a ⋖ b -> f b < f a
参数：f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `strictMono_iff_forall_covBy`：strictMono_iff_forall_covBy [Preorder α] [L
ocallyFiniteOrder α] [Preorder β] (f : α -> β) : StrictMono f ↔ forall a b : α, 
a ⋖ b -> f a < f …

--- 原说明 ---
A function from a locally finite preorder is strictly antitone if and only if it
 is strictly
antitone when restricted to pairs satisfying `a ⋖ b`.
-/
lemma strictAnti_iff_forall_covBy [Preorder α] [LocallyFiniteOrder α] [Preorder β]
    (f : α → β) : StrictAnti f ↔ ∀ a b : α, a ⋖ b → f b < f a :=
  strictMono_iff_forall_covBy (β := βᵒᵈ) f

end Cover

