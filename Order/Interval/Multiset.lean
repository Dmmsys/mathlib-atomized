/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Interval.Finset.Basic

/-!
# Intervals as multisets

This file defines intervals as multisets.

## Main declarations

In a `LocallyFiniteOrder`,
* `Multiset.Icc`: Closed-closed interval as a multiset.
* `Multiset.Ico`: Closed-open interval as a multiset.
* `Multiset.Ioc`: Open-closed interval as a multiset.
* `Multiset.Ioo`: Open-open interval as a multiset.

In a `LocallyFiniteOrderTop`,
* `Multiset.Ici`: Closed-infinite interval as a multiset.
* `Multiset.Ioi`: Open-infinite interval as a multiset.

In a `LocallyFiniteOrderBot`,
* `Multiset.Iic`: Infinite-open interval as a multiset.
* `Multiset.Iio`: Infinite-closed interval as a multiset.

## TODO

Do we really need this file at all? (March 2024)
-/

@[expose] public section


variable {α : Type*}

namespace Multiset

section LocallyFiniteOrder
variable [Preorder α] [LocallyFiniteOrder α] {a b x : α}

/-- The multiset of elements `x` such that `a ≤ x` and `x ≤ b`. Basically `Set.Icc a b` as a
multiset. -/
/-
**Multiset.Icc** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：Icc (a b : α) : Multiset α
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiset of elements `x` such that `a ≤ x` and `x ≤ b`. Basically `Set.Icc a
 b` as a
multiset.
-/
def Icc (a b : α) : Multiset α := (Finset.Icc a b).val

/-- The multiset of elements `x` such that `a ≤ x` and `x < b`. Basically `Set.Ico a b` as a
multiset. -/
/-
**Multiset.Ico** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：Ico (a b : α) : Multiset α
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiset of elements `x` such that `a ≤ x` and `x < b`. Basically `Set.Ico a
 b` as a
multiset.
-/
def Ico (a b : α) : Multiset α := (Finset.Ico a b).val

/-- The multiset of elements `x` such that `a < x` and `x ≤ b`. Basically `Set.Ioc a b` as a
multiset. -/
/-
**Multiset.Ioc** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：Ioc (a b : α) : Multiset α
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiset of elements `x` such that `a < x` and `x ≤ b`. Basically `Set.Ioc a
 b` as a
multiset.
-/
def Ioc (a b : α) : Multiset α := (Finset.Ioc a b).val

/-- The multiset of elements `x` such that `a < x` and `x < b`. Basically `Set.Ioo a b` as a
multiset. -/
/-
**Multiset.Ioo** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：Ioo (a b : α) : Multiset α
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiset of elements `x` such that `a < x` and `x < b`. Basically `Set.Ioo a
 b` as a
multiset.
-/
def Ioo (a b : α) : Multiset α := (Finset.Ioo a b).val
/-
**Multiset.mem_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFiniteOrder α] {a b 
x : α}, x ∈ Multiset.Icc a b ↔ a ≤ x ∧ x ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Icc.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Icc a b = (Finset.Icc a b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_def`：mem_def {a : α} {s : Finset α} : a in s ↔ a in s.1
· 使用定理 `Finset.mem_Icc`：mem_Icc : x in Icc a b ↔ a <= x ∧ x <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_Icc : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b := by rw [Icc, ← Finset.mem_def, Finset.mem_Icc]
/-
**Multiset.mem_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFiniteOrder α] {a b 
x : α}, x ∈ Multiset.Ico a b ↔ a ≤ x ∧ x < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ico.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ico a b = (Finset.Ico a b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_def`：mem_def {a : α} {s : Finset α} : a in s ↔ a in s.1
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_Ico : x ∈ Ico a b ↔ a ≤ x ∧ x < b := by rw [Ico, ← Finset.mem_def, Finset.mem_Ico]
/-
**Multiset.mem_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFiniteOrder α] {a b 
x : α}, x ∈ Multiset.Ioc a b ↔ a < x ∧ x ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ioc.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ioc a b = (Finset.Ioc a b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_def`：mem_def {a : α} {s : Finset α} : a in s ↔ a in s.1
· 使用定理 `Finset.mem_Ioc`：mem_Ioc : x in Ioc a b ↔ a < x ∧ x <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_Ioc : x ∈ Ioc a b ↔ a < x ∧ x ≤ b := by rw [Ioc, ← Finset.mem_def, Finset.mem_Ioc]
/-
**Multiset.mem_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFiniteOrder α] {a b 
x : α}, x ∈ Multiset.Ioo a b ↔ a < x ∧ x < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ioo.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ioo a b = (Finset.Ioo a b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_def`：mem_def {a : α} {s : Finset α} : a in s ↔ a in s.1
· 使用定理 `Finset.mem_Ioo`：mem_Ioo : x in Ioo a b ↔ a < x ∧ x < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_Ioo : x ∈ Ioo a b ↔ a < x ∧ x < b := by rw [Ioo, ← Finset.mem_def, Finset.mem_Ioo]

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [Preorder α] [LocallyFiniteOrderTop α] {a x : α}

/-- The multiset of elements `x` such that `a ≤ x`. Basically `Set.Ici a` as a multiset. -/
/-
**Multiset.Ici** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：Ici (a : α) : Multiset α
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiset of elements `x` such that `a ≤ x`. Basically `Set.Ici a` as a multi
set.
-/
def Ici (a : α) : Multiset α := (Finset.Ici a).val

/-- The multiset of elements `x` such that `a < x`. Basically `Set.Ioi a` as a multiset. -/
/-
**Multiset.Ioi** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：Ioi (a : α) : Multiset α
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiset of elements `x` such that `a < x`. Basically `Set.Ioi a` as a multi
set.
-/
def Ioi (a : α) : Multiset α := (Finset.Ioi a).val
/-
**Multiset.mem_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFiniteOrderTop α] {a
 x : α}, x ∈ Multiset.Ici a ↔ a ≤ x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ici.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrderTop α] (a : α), Multiset.Ici a = (Finset.Ici a).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_def`：mem_def {a : α} {s : Finset α} : a in s ↔ a in s.1
· 使用定理 `Finset.mem_Ici`：mem_Ici : x in Ici a ↔ a <= x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_Ici : x ∈ Ici a ↔ a ≤ x := by rw [Ici, ← Finset.mem_def, Finset.mem_Ici]
/-
**Multiset.mem_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFiniteOrderTop α] {a
 x : α}, x ∈ Multiset.Ioi a ↔ a < x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ioi.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrderTop α] (a : α), Multiset.Ioi a = (Finset.Ioi a).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_def`：mem_def {a : α} {s : Finset α} : a in s ↔ a in s.1
· 使用定理 `Finset.mem_Ioi`：mem_Ioi : x in Ioi a ↔ a < x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_Ioi : x ∈ Ioi a ↔ a < x := by rw [Ioi, ← Finset.mem_def, Finset.mem_Ioi]

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot
variable [Preorder α] [LocallyFiniteOrderBot α] {b x : α}

/-- The multiset of elements `x` such that `x ≤ b`. Basically `Set.Iic b` as a multiset. -/
/-
**Multiset.Iic** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：Iic (b : α) : Multiset α
参数：b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiset of elements `x` such that `x ≤ b`. Basically `Set.Iic b` as a multi
set.
-/
def Iic (b : α) : Multiset α := (Finset.Iic b).val

/-- The multiset of elements `x` such that `x < b`. Basically `Set.Iio b` as a multiset. -/
/-
**Multiset.Iio** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：Iio (b : α) : Multiset α
参数：b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiset of elements `x` such that `x < b`. Basically `Set.Iio b` as a multi
set.
-/
def Iio (b : α) : Multiset α := (Finset.Iio b).val
/-
**Multiset.mem_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFiniteOrderBot α] {b
 x : α}, x ∈ Multiset.Iic b ↔ x ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Iic.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrderBot α] (b : α), Multiset.Iic b = (Finset.Iic b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_def`：mem_def {a : α} {s : Finset α} : a in s ↔ a in s.1
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_Iic : x ∈ Iic b ↔ x ≤ b := by rw [Iic, ← Finset.mem_def, Finset.mem_Iic]
/-
**Multiset.mem_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFiniteOrderBot α] {b
 x : α}, x ∈ Multiset.Iio b ↔ x < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Iio.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrderBot α] (b : α), Multiset.Iio b = (Finset.Iio b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_def`：mem_def {a : α} {s : Finset α} : a in s ↔ a in s.1
· 使用定理 `Finset.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iio a ↔ x < a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_Iio : x ∈ Iio b ↔ x < b := by rw [Iio, ← Finset.mem_def, Finset.mem_Iio]

end LocallyFiniteOrderBot

section Preorder

variable [Preorder α] [LocallyFiniteOrder α] {a b c : α}

/-
**Multiset.nodup_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：nodup_Icc : (Icc a b).Nodup
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
theorem nodup_Icc : (Icc a b).Nodup :=
  Finset.nodup _
/-
**Multiset.nodup_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：nodup_Ico : (Ico a b).Nodup
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
theorem nodup_Ico : (Ico a b).Nodup :=
  Finset.nodup _
/-
**Multiset.nodup_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：nodup_Ioc : (Ioc a b).Nodup
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
theorem nodup_Ioc : (Ioc a b).Nodup :=
  Finset.nodup _
/-
**Multiset.nodup_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：nodup_Ioo : (Ioo a b).Nodup
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
theorem nodup_Ioo : (Ioo a b).Nodup :=
  Finset.nodup _

@[simp]
/-
**Multiset.Icc_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Icc_eq_zero_iff : Icc a b = 0 ↔ ¬a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Icc.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Icc a b = (Finset.Icc a b).val
· 使用定理 `Finset.val_eq_zero`：val_eq_zero {s : Finset α} : s.1 = 0 ↔ s = ∅
· 使用定理 `Finset.Icc_eq_empty_iff`：Icc_eq_empty_iff : Icc a b = ∅ ↔ ¬a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Icc_eq_zero_iff : Icc a b = 0 ↔ ¬a ≤ b := by
  rw [Icc, Finset.val_eq_zero, Finset.Icc_eq_empty_iff]

@[simp]
/-
**Multiset.Ico_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ico_eq_zero_iff : Ico a b = 0 ↔ ¬a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ico.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ico a b = (Finset.Ico a b).val
· 使用定理 `Finset.val_eq_zero`：val_eq_zero {s : Finset α} : s.1 = 0 ↔ s = ∅
· 使用定理 `Finset.Ico_eq_empty_iff`：Ico_eq_empty_iff : Ico a b = ∅ ↔ ¬a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Ico_eq_zero_iff : Ico a b = 0 ↔ ¬a < b := by
  rw [Ico, Finset.val_eq_zero, Finset.Ico_eq_empty_iff]

@[simp]
/-
**Multiset.Ioc_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ioc_eq_zero_iff : Ioc a b = 0 ↔ ¬a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ioc.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ioc a b = (Finset.Ioc a b).val
· 使用定理 `Finset.val_eq_zero`：val_eq_zero {s : Finset α} : s.1 = 0 ↔ s = ∅
· 使用定理 `Finset.Ioc_eq_empty_iff`：Ioc_eq_empty_iff : Ioc a b = ∅ ↔ ¬a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Ioc_eq_zero_iff : Ioc a b = 0 ↔ ¬a < b := by
  rw [Ioc, Finset.val_eq_zero, Finset.Ioc_eq_empty_iff]

@[simp]
/-
**Multiset.Ioo_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ioo_eq_zero_iff [DenselyOrdered α] : Ioo a b = 0 ↔ ¬a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ioo.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ioo a b = (Finset.Ioo a b).val
· 使用定理 `Finset.val_eq_zero`：val_eq_zero {s : Finset α} : s.1 = 0 ↔ s = ∅
· 使用定理 `Finset.Ioo_eq_empty_iff`：Ioo_eq_empty_iff [DenselyOrdered α] : Ioo a b =
 ∅ ↔ ¬a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Ioo_eq_zero_iff [DenselyOrdered α] : Ioo a b = 0 ↔ ¬a < b := by
  rw [Ioo, Finset.val_eq_zero, Finset.Ioo_eq_empty_iff]

alias ⟨_, Icc_eq_zero⟩ := Icc_eq_zero_iff

alias ⟨_, Ico_eq_zero⟩ := Ico_eq_zero_iff

alias ⟨_, Ioc_eq_zero⟩ := Ioc_eq_zero_iff

@[simp]
/-
**Multiset.Ioo_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ioo_eq_zero (h : ¬a < b) : Ioo a b = 0
参数：h : ¬a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.eq_zero_iff_forall_notMem`：eq_zero_iff_forall_notMem {s : Multi
set α} : s = 0 ↔ forall a, a ∉ s
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_Ioo`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locally
FiniteOrder α] {a b x : α}, x ∈ Multiset.Ioo a b ↔ a < x ∧ x < b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Ioo_eq_zero (h : ¬a < b) : Ioo a b = 0 :=
  eq_zero_iff_forall_notMem.2 fun _x hx => h ((mem_Ioo.1 hx).1.trans (mem_Ioo.1 hx).2)

@[simp]
/-
**Multiset.Icc_eq_zero_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Icc_eq_zero_of_lt (h : b < a) : Icc a b = 0
参数：h : b < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Icc_eq_zero`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Loc
allyFiniteOrder α] {a b : α}, ¬a ≤ b → Multiset.Icc a b = 0
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem Icc_eq_zero_of_lt (h : b < a) : Icc a b = 0 :=
  Icc_eq_zero h.not_ge

@[simp]
/-
**Multiset.Ico_eq_zero_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ico_eq_zero_of_le (h : b <= a) : Ico a b = 0
参数：h : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Ico_eq_zero`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Loc
allyFiniteOrder α] {a b : α}, ¬a < b → Multiset.Ico a b = 0
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
-/
theorem Ico_eq_zero_of_le (h : b ≤ a) : Ico a b = 0 :=
  Ico_eq_zero h.not_gt

@[simp]
/-
**Multiset.Ioc_eq_zero_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ioc_eq_zero_of_le (h : b <= a) : Ioc a b = 0
参数：h : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Ioc_eq_zero`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Loc
allyFiniteOrder α] {a b : α}, ¬a < b → Multiset.Ioc a b = 0
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
-/
theorem Ioc_eq_zero_of_le (h : b ≤ a) : Ioc a b = 0 :=
  Ioc_eq_zero h.not_gt

@[simp]
/-
**Multiset.Ioo_eq_zero_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ioo_eq_zero_of_le (h : b <= a) : Ioo a b = 0
参数：h : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Ioo_eq_zero`：Ioo_eq_zero (h : ¬a < b) : Ioo a b = 0
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
-/
theorem Ioo_eq_zero_of_le (h : b ≤ a) : Ioo a b = 0 :=
  Ioo_eq_zero h.not_gt

variable (a)
/-
**Multiset.Ico_self** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ico_self : Ico a a = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ico.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ico a b = (Finset.Ico a b).val
· 使用定理 `Finset.Ico_self`：Ico_self : Ico a a = ∅
· 使用定理 `Finset.empty_val`：empty_val : (∅ : Finset α).1 = 0
-/
theorem Ico_self : Ico a a = 0 := by rw [Ico, Finset.Ico_self, Finset.empty_val]
/-
**Multiset.Ioc_self** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ioc_self : Ioc a a = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ioc.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ioc a b = (Finset.Ioc a b).val
· 使用定理 `Finset.Ioc_self`：Ioc_self : Ioc a a = ∅
· 使用定理 `Finset.empty_val`：empty_val : (∅ : Finset α).1 = 0
-/
theorem Ioc_self : Ioc a a = 0 := by rw [Ioc, Finset.Ioc_self, Finset.empty_val]
/-
**Multiset.Ioo_self** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ioo_self : Ioo a a = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ioo.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ioo a b = (Finset.Ioo a b).val
· 使用定理 `Finset.Ioo_self`：Ioo_self : Ioo a a = ∅
· 使用定理 `Finset.empty_val`：empty_val : (∅ : Finset α).1 = 0
-/
theorem Ioo_self : Ioo a a = 0 := by rw [Ioo, Finset.Ioo_self, Finset.empty_val]

variable {a}
/-
**Multiset.left_mem_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：left_mem_Icc : a in Icc a b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.left_mem_Icc`：left_mem_Icc : a in Icc a b ↔ a <= b
-/
theorem left_mem_Icc : a ∈ Icc a b ↔ a ≤ b :=
  Finset.left_mem_Icc
/-
**Multiset.left_mem_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：left_mem_Ico : a in Ico a b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.left_mem_Ico`：left_mem_Ico : a in Ico a b ↔ a < b
-/
theorem left_mem_Ico : a ∈ Ico a b ↔ a < b :=
  Finset.left_mem_Ico
/-
**Multiset.right_mem_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：right_mem_Icc : b in Icc a b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.right_mem_Icc`：right_mem_Icc : b in Icc a b ↔ a <= b
-/
theorem right_mem_Icc : b ∈ Icc a b ↔ a ≤ b :=
  Finset.right_mem_Icc
/-
**Multiset.right_mem_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：right_mem_Ioc : b in Ioc a b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.right_mem_Ioc`：right_mem_Ioc : b in Ioc a b ↔ a < b
-/
theorem right_mem_Ioc : b ∈ Ioc a b ↔ a < b :=
  Finset.right_mem_Ioc
/-
**Multiset.left_notMem_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：left_notMem_Ioc : a ∉ Ioc a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.left_notMem_Ioc`：left_notMem_Ioc : a ∉ Ioc a b
-/
theorem left_notMem_Ioc : a ∉ Ioc a b :=
  Finset.left_notMem_Ioc
/-
**Multiset.left_notMem_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：left_notMem_Ioo : a ∉ Ioo a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.left_notMem_Ioo`：left_notMem_Ioo : a ∉ Ioo a b
-/
theorem left_notMem_Ioo : a ∉ Ioo a b :=
  Finset.left_notMem_Ioo
/-
**Multiset.right_notMem_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：right_notMem_Ico : b ∉ Ico a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.right_notMem_Ico`：right_notMem_Ico : b ∉ Ico a b
-/
theorem right_notMem_Ico : b ∉ Ico a b :=
  Finset.right_notMem_Ico
/-
**Multiset.right_notMem_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：right_notMem_Ioo : b ∉ Ioo a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.right_notMem_Ioo`：right_notMem_Ioo : b ∉ Ioo a b
-/
theorem right_notMem_Ioo : b ∉ Ioo a b :=
  Finset.right_notMem_Ioo
/-
**Multiset.Ico_filter_lt_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ico_filter_lt_of_le_left [DecidablePred (· < c)] (hca : c <= a) : ((Ico a 
b).filter fun x => x < c) = ∅
参数：· < c；hca : c <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ico.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ico a b = (Finset.Ico a b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.filter_val`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α),   (Finset.filter p s).val = Multiset.filter p s.val
· 使用定理 `Finset.Ico_filter_lt_of_le_left`：Ico_filter_lt_of_le_left [DecidablePred
 (· < c)] (hca : c <= a) : {x in Ico a b | x < c} = ∅
-/
theorem Ico_filter_lt_of_le_left [DecidablePred (· < c)] (hca : c ≤ a) :
    ((Ico a b).filter fun x => x < c) = ∅ := by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_lt_of_le_left hca]
  rfl
/-
**Multiset.Ico_filter_lt_of_right_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ico_filter_lt_of_right_le [DecidablePred (· < c)] (hbc : b <= c) : ((Ico a
 b).filter fun x => x < c) = Ico a b
参数：· < c；hbc : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ico.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ico a b = (Finset.Ico a b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.filter_val`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α),   (Finset.filter p s).val = Multiset.filter p s.val
· 使用定理 `Finset.Ico_filter_lt_of_right_le`：Ico_filter_lt_of_right_le [DecidablePr
ed (· < c)] (hbc : b <= c) : {x in Ico a b | x < c} = Ico a b
-/
theorem Ico_filter_lt_of_right_le [DecidablePred (· < c)] (hbc : b ≤ c) :
    ((Ico a b).filter fun x => x < c) = Ico a b := by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_lt_of_right_le hbc]
/-
**Multiset.Ico_filter_lt_of_le_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ico_filter_lt_of_le_right [DecidablePred (· < c)] (hcb : c <= b) : ((Ico a
 b).filter fun x => x < c) = Ico a c
参数：· < c；hcb : c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ico.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ico a b = (Finset.Ico a b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.filter_val`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α),   (Finset.filter p s).val = Multiset.filter p s.val
· 使用定理 `Finset.Ico_filter_lt_of_le_right`：Ico_filter_lt_of_le_right [DecidablePr
ed (· < c)] (hcb : c <= b) : {x in Ico a b | x < c} = Ico a c
-/
theorem Ico_filter_lt_of_le_right [DecidablePred (· < c)] (hcb : c ≤ b) :
    ((Ico a b).filter fun x => x < c) = Ico a c := by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_lt_of_le_right hcb]
  rfl
/-
**Multiset.Ico_filter_le_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ico_filter_le_of_le_left [DecidablePred (c <= ·)] (hca : c <= a) : ((Ico a
 b).filter fun x => c <= x) = Ico a b
参数：c <= ·；hca : c <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ico.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ico a b = (Finset.Ico a b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.filter_val`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α),   (Finset.filter p s).val = Multiset.filter p s.val
· 使用定理 `Finset.Ico_filter_le_of_le_left`：Ico_filter_le_of_le_left {a b c : α} [D
ecidablePred (c <= ·)] (hca : c <= a) : {x in Ico a b | c <= x} = Ico a b
-/
theorem Ico_filter_le_of_le_left [DecidablePred (c ≤ ·)] (hca : c ≤ a) :
    ((Ico a b).filter fun x => c ≤ x) = Ico a b := by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_le_of_le_left hca]
/-
**Multiset.Ico_filter_le_of_right_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ico_filter_le_of_right_le [DecidablePred (b <= ·)] : ((Ico a b).filter fun
 x => b <= x) = ∅
参数：b <= ·。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ico.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ico a b = (Finset.Ico a b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.filter_val`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α),   (Finset.filter p s).val = Multiset.filter p s.val
· 使用定理 `Finset.Ico_filter_le_of_right_le`：Ico_filter_le_of_right_le {a b : α} [D
ecidablePred (b <= ·)] : {x in Ico a b | b <= x} = ∅
-/
theorem Ico_filter_le_of_right_le [DecidablePred (b ≤ ·)] :
    ((Ico a b).filter fun x => b ≤ x) = ∅ := by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_le_of_right_le]
  rfl
/-
**Multiset.Ico_filter_le_of_left_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ico_filter_le_of_left_le [DecidablePred (c <= ·)] (hac : a <= c) : ((Ico a
 b).filter fun x => c <= x) = Ico c b
参数：c <= ·；hac : a <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ico.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ico a b = (Finset.Ico a b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.filter_val`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α),   (Finset.filter p s).val = Multiset.filter p s.val
· 使用定理 `Finset.Ico_filter_le_of_left_le`：Ico_filter_le_of_left_le {a b c : α} [D
ecidablePred (c <= ·)] (hac : a <= c) : {x in Ico a b | c <= x} = Ico c b
-/
theorem Ico_filter_le_of_left_le [DecidablePred (c ≤ ·)] (hac : a ≤ c) :
    ((Ico a b).filter fun x => c ≤ x) = Ico c b := by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_le_of_left_le hac]
  rfl

end Preorder

section PartialOrder

variable [PartialOrder α] [LocallyFiniteOrder α] {a b : α}

@[simp]
/-
**Multiset.Icc_self** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Icc_self (a : α) : Icc a a = {a}
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Icc.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Icc a b = (Finset.Icc a b).val
· 使用定理 `Finset.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `Finset.singleton_val`：singleton_val (a : α) : ({a} : Finset α).1 = {a}
-/
theorem Icc_self (a : α) : Icc a a = {a} := by rw [Icc, Finset.Icc_self, Finset.singleton_val]
/-
**Multiset.Ico_cons_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ico_cons_right (h : a <= b) : b ::ₘ Ico a b = Icc a b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ico.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ico a b = (Finset.Ico a b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_val_of_notMem`：insert_val_of_notMem {a : α} {s : Finset α}
 (h : a ∉ s) : (insert a s).1 = a ::ₘ s.1
· 使用定理 `Multiset.right_notMem_Ico`：right_notMem_Ico : b ∉ Ico a b
· 使用定理 `Finset.Ico_insert_right`：Ico_insert_right (h : a <= b) : insert b (Ico a
 b) = Icc a b
-/
theorem Ico_cons_right (h : a ≤ b) : b ::ₘ Ico a b = Icc a b := by
  classical
    rw [Ico, ← Finset.insert_val_of_notMem right_notMem_Ico, Finset.Ico_insert_right h]
    rfl
/-
**Multiset.Ioo_cons_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ioo_cons_left (h : a < b) : a ::ₘ Ioo a b = Ico a b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ioo.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ioo a b = (Finset.Ioo a b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_val_of_notMem`：insert_val_of_notMem {a : α} {s : Finset α}
 (h : a ∉ s) : (insert a s).1 = a ::ₘ s.1
· 使用定理 `Multiset.left_notMem_Ioo`：left_notMem_Ioo : a ∉ Ioo a b
· 使用定理 `Finset.Ioo_insert_left`：Ioo_insert_left (h : a < b) : insert a (Ioo a b)
 = Ico a b
-/
theorem Ioo_cons_left (h : a < b) : a ::ₘ Ioo a b = Ico a b := by
  classical
    rw [Ioo, ← Finset.insert_val_of_notMem left_notMem_Ioo, Finset.Ioo_insert_left h]
    rfl
/-
**Multiset.Ico_disjoint_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ico_disjoint_Ico {a b c d : α} (h : b <= c) : Disjoint (Ico a b) (Ico c d)
参数：h : b <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.disjoint_left`：disjoint_left {s t : Multiset α} : Disjoint s t 
↔ forall {a}, a in s -> a ∉ t
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locally
FiniteOrder α] {a b x : α}, x ∈ Multiset.Ico a b ↔ a ≤ x ∧ x < b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Ico_disjoint_Ico {a b c d : α} (h : b ≤ c) : Disjoint (Ico a b) (Ico c d) :=
  disjoint_left.mpr fun hab hbc => by
    rw [mem_Ico] at hab hbc
    exact hab.2.not_ge (h.trans hbc.1)

@[simp]
/-
**Multiset.Ico_inter_Ico_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ico_inter_Ico_of_le [DecidableEq α] {a b c d : α} (h : b <= c) : Ico a b i
nter Ico c d = 0
参数：h : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.inter_eq_zero_iff_disjoint`：inter_eq_zero_iff_disjoint [Decidab
leEq α] {s t : Multiset α} : s inter t = 0 ↔ Disjoint s t
· 使用定理 `Multiset.Ico_disjoint_Ico`：Ico_disjoint_Ico {a b c d : α} (h : b <= c) :
 Disjoint (Ico a b) (Ico c d)
-/
theorem Ico_inter_Ico_of_le [DecidableEq α] {a b c d : α} (h : b ≤ c) : Ico a b ∩ Ico c d = 0 :=
  Multiset.inter_eq_zero_iff_disjoint.2 <| Ico_disjoint_Ico h
/-
**Multiset.Ico_filter_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ico_filter_le_left {a b : α} [DecidablePred (· <= a)] (hab : a < b) : ((Ic
o a b).filter fun x => x <= a) = {a}
参数：· <= a；hab : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ico.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ico a b = (Finset.Ico a b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.filter_val`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α),   (Finset.filter p s).val = Multiset.filter p s.val
· 使用定理 `Finset.Ico_filter_le_left`：Ico_filter_le_left {a b : α} [DecidablePred (
· <= a)] (hab : a < b) : {x in Ico a b | x <= a} = {a}
-/
theorem Ico_filter_le_left {a b : α} [DecidablePred (· ≤ a)] (hab : a < b) :
    ((Ico a b).filter fun x => x ≤ a) = {a} := by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_le_left hab]
  rfl
/-
**Multiset.card_Ico_eq_card_Icc_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_Ico_eq_card_Icc_sub_one (a b : α) : card (Ico a b) = card (Icc a b) -
 1
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_Ico_eq_card_Icc_sub_one`：card_Ico_eq_card_Icc_sub_one (a b :
 α) : #(Ico a b) = #(Icc a b) - 1
-/
theorem card_Ico_eq_card_Icc_sub_one (a b : α) : card (Ico a b) = card (Icc a b) - 1 :=
  Finset.card_Ico_eq_card_Icc_sub_one _ _
/-
**Multiset.card_Ioc_eq_card_Icc_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_Ioc_eq_card_Icc_sub_one (a b : α) : card (Ioc a b) = card (Icc a b) -
 1
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_Ioc_eq_card_Icc_sub_one`：card_Ioc_eq_card_Icc_sub_one (a b :
 α) : #(Ioc a b) = #(Icc a b) - 1
-/
theorem card_Ioc_eq_card_Icc_sub_one (a b : α) : card (Ioc a b) = card (Icc a b) - 1 :=
  Finset.card_Ioc_eq_card_Icc_sub_one _ _
/-
**Multiset.card_Ioo_eq_card_Ico_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_Ioo_eq_card_Ico_sub_one (a b : α) : card (Ioo a b) = card (Ico a b) -
 1
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_Ioo_eq_card_Ico_sub_one`：card_Ioo_eq_card_Ico_sub_one (a b :
 α) : #(Ioo a b) = #(Ico a b) - 1
-/
theorem card_Ioo_eq_card_Ico_sub_one (a b : α) : card (Ioo a b) = card (Ico a b) - 1 :=
  Finset.card_Ioo_eq_card_Ico_sub_one _ _
/-
**Multiset.card_Ioo_eq_card_Icc_sub_two** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_Ioo_eq_card_Icc_sub_two (a b : α) : card (Ioo a b) = card (Icc a b) -
 2
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_Ioo_eq_card_Icc_sub_two`：card_Ioo_eq_card_Icc_sub_two (a b :
 α) : #(Ioo a b) = #(Icc a b) - 2
-/
theorem card_Ioo_eq_card_Icc_sub_two (a b : α) : card (Ioo a b) = card (Icc a b) - 2 :=
  Finset.card_Ioo_eq_card_Icc_sub_two _ _

end PartialOrder

section LinearOrder

variable [LinearOrder α] [LocallyFiniteOrder α] {a b c d : α}

/-
**Multiset.Ico_subset_Ico_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ico_subset_Ico_iff {a₁ b₁ a₂ b₂ : α} (h : a₁ < b₁) : Ico a₁ b₁ subseteq Ic
o a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ <= b₂
参数：h : a₁ < b₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Ico_subset_Ico_iff`：Ico_subset_Ico_iff {a₁ b₁ a₂ b₂ : α} (h : a₁ 
< b₁) : Ico a₁ b₁ subseteq Ico a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ <= b₂
-/
theorem Ico_subset_Ico_iff {a₁ b₁ a₂ b₂ : α} (h : a₁ < b₁) :
    Ico a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
  Finset.Ico_subset_Ico_iff h
/-
**Multiset.Ico_add_Ico_eq_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ico_add_Ico_eq_Ico {a b c : α} (hab : a <= b) (hbc : b <= c) : Ico a b + I
co b c = Ico a c
参数：hab : a <= b；hbc : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.add_eq_union_iff_disjoint`：add_eq_union_iff_disjoint [Decidable
Eq α] {s t : Multiset α} : s + t = s union t ↔ Disjoint s t
· 使用定理 `Multiset.Ico_disjoint_Ico`：Ico_disjoint_Ico {a b c d : α} (h : b <= c) :
 Disjoint (Ico a b) (Ico c d)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Multiset.Ico.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ico a b = (Finset.Ico a b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.union_val`：union_val (s t : Finset α) : (s union t).1 = s.1 union
 t.1
· 使用定理 `Finset.Ico_union_Ico_eq_Ico`：Ico_union_Ico_eq_Ico {a b c : α} (hab : a <
= b) (hbc : b <= c) : Ico a b union Ico b c = Ico a c
-/
theorem Ico_add_Ico_eq_Ico {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
    Ico a b + Ico b c = Ico a c := by
  rw [add_eq_union_iff_disjoint.2 (Ico_disjoint_Ico le_rfl), Ico, Ico, Ico, ← Finset.union_val,
    Finset.Ico_union_Ico_eq_Ico hab hbc]
/-
**Multiset.Ico_inter_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ico_inter_Ico : Ico a b inter Ico c d = Ico (max a c) (min b d)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ico.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ico a b = (Finset.Ico a b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.inter_val`：inter_val (s₁ s₂ : Finset α) : (s₁ inter s₂).1 = s₁.1 
inter s₂.1
· 使用定理 `Finset.Ico_inter_Ico`：Ico_inter_Ico {a b c d : α} : Ico a b inter Ico c 
d = Ico (max a c) (min b d)
-/
theorem Ico_inter_Ico : Ico a b ∩ Ico c d = Ico (max a c) (min b d) := by
  rw [Ico, Ico, Ico, ← Finset.inter_val, Finset.Ico_inter_Ico]

@[simp]
/-
**Multiset.Ico_filter_lt** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ico_filter_lt (a b c : α) : ((Ico a b).filter fun x => x < c) = Ico a (min
 b c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ico.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ico a b = (Finset.Ico a b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.filter_val`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α),   (Finset.filter p s).val = Multiset.filter p s.val
· 使用定理 `Finset.Ico_filter_lt`：Ico_filter_lt (a b c : α) : {x in Ico a b | x < c}
 = Ico a (min b c)
-/
theorem Ico_filter_lt (a b c : α) : ((Ico a b).filter fun x => x < c) = Ico a (min b c) := by
  rw [Ico, Ico, ← Finset.filter_val, Finset.Ico_filter_lt]

@[simp]
/-
**Multiset.Ico_filter_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ico_filter_le (a b c : α) : ((Ico a b).filter fun x => c <= x) = Ico (max 
a c) b
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ico.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ico a b = (Finset.Ico a b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.filter_val`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α),   (Finset.filter p s).val = Multiset.filter p s.val
· 使用定理 `Finset.Ico_filter_le`：Ico_filter_le (a b c : α) : {x in Ico a b | c <= x
} = Ico (max a c) b
-/
theorem Ico_filter_le (a b c : α) : ((Ico a b).filter fun x => c ≤ x) = Ico (max a c) b := by
  rw [Ico, Ico, ← Finset.filter_val, Finset.Ico_filter_le]

@[simp]
/-
**Multiset.Ico_sub_Ico_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ico_sub_Ico_left (a b c : α) : Ico a b - Ico a c = Ico (max a c) b
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ico.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ico a b = (Finset.Ico a b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sdiff_val`：sdiff_val (s₁ s₂ : Finset α) : (s₁ \ s₂).val = s₁.val 
- s₂.val
· 使用定理 `Finset.Ico_sdiff_Ico_left`：Ico_sdiff_Ico_left (a b c : α) : Ico a b \ Ic
o a c = Ico (max a c) b
-/
theorem Ico_sub_Ico_left (a b c : α) : Ico a b - Ico a c = Ico (max a c) b := by
  rw [Ico, Ico, Ico, ← Finset.sdiff_val, Finset.Ico_sdiff_Ico_left]

@[simp]
/-
**Multiset.Ico_sub_Ico_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：Ico_sub_Ico_right (a b c : α) : Ico a b - Ico c b = Ico a (min b c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ico.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ico a b = (Finset.Ico a b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sdiff_val`：sdiff_val (s₁ s₂ : Finset α) : (s₁ \ s₂).val = s₁.val 
- s₂.val
· 使用定理 `Finset.Ico_sdiff_Ico_right`：Ico_sdiff_Ico_right (a b c : α) : Ico a b \ 
Ico c b = Ico a (min b c)
-/
theorem Ico_sub_Ico_right (a b c : α) : Ico a b - Ico c b = Ico a (min b c) := by
  rw [Ico, Ico, Ico, ← Finset.sdiff_val, Finset.Ico_sdiff_Ico_right]

end LinearOrder
end Multiset

