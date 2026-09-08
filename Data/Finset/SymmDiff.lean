/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Set.SymmDiff

/-!
# Symmetric difference of finite sets

This file concerns the symmetric difference operator `s Δ t` on finite sets.

## Tags

finite sets, finset

-/

public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice Monoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

/-! ### Symmetric difference -/

section SymmDiff

open scoped symmDiff

variable [DecidableEq α] {s t : Finset α} {a b : α}

/-
**Finset.mem_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_symmDiff : a in s ∆ t ↔ a in s ∧ a ∉ t ∨ a in t ∧ a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_symmDiff : a ∈ s ∆ t ↔ a ∈ s ∧ a ∉ t ∨ a ∈ t ∧ a ∉ s := by
  simp_rw [symmDiff, sup_eq_union, mem_union, mem_sdiff]
/-
**Finset.symmDiff_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (s t : Finset α), symmDiff s t = s
 \ t ∪ t \ s
参数：s t : Finset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem symmDiff_def (s t : Finset α) : s ∆ t = s \ t ∪ t \ s := rfl

@[simp, norm_cast]
/-
**Finset.coe_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_symmDiff : (↑(s ∆ t) : Set α) = (s : Set α) ∆ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_symmDiff : (↑(s ∆ t) : Set α) = (s : Set α) ∆ t :=
  Set.ext fun x => by simp [mem_symmDiff, Set.mem_symmDiff]
/-
**Finset.symmDiff_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α}, symmDiff s t = ∅
 ↔ s = t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_eq_bot`：symmDiff_eq_bot {a b : α} : a ∆ b = ⊥ ↔ a = b
-/
@[simp] lemma symmDiff_eq_empty : s ∆ t = ∅ ↔ s = t := symmDiff_eq_bot
/-
**Finset.symmDiff_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α}, (symmDiff s t).N
onempty ↔ s ≠ t
参数：symmDiff s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Finset.symmDiff_eq_empty`：∀ {α : Type u_1} [inst : DecidableEq α] {s t :
 Finset α}, symmDiff s t = ∅ ↔ s = t
-/
@[simp] lemma symmDiff_nonempty : (s ∆ t).Nonempty ↔ s ≠ t :=
  nonempty_iff_ne_empty.trans symmDiff_eq_empty.not
/-
**Finset.image_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_symmDiff [DecidableEq β] {f : α -> β} (s t : Finset α) (hf : Injecti
ve f) : (s ∆ t).image f = s.image f ∆ t.image f
参数：s t : Finset α；hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_symmDiff`：image_symmDiff (hf : Injective f) (s t : Set α) : f 
'' s ∆ t = (f '' s) ∆ (f '' t)
-/
theorem image_symmDiff [DecidableEq β] {f : α → β} (s t : Finset α) (hf : Injective f) :
    (s ∆ t).image f = s.image f ∆ t.image f :=
  mod_cast Set.image_symmDiff hf s t

/-- See `symmDiff_subset_sdiff'` for the swapped version of this. -/
/-
**Finset.symmDiff_subset_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：symmDiff_subset_sdiff : s \ t subseteq s ∆ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂

--- 原说明 ---
See `symmDiff_subset_sdiff'` for the swapped version of this.
-/
lemma symmDiff_subset_sdiff : s \ t ⊆ s ∆ t := subset_union_left

/-- See `symmDiff_subset_sdiff` for the swapped version of this. -/
/-
**Finset.symmDiff_subset_sdiff'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：symmDiff_subset_sdiff' : t \ s subseteq s ∆ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂

--- 原说明 ---
See `symmDiff_subset_sdiff` for the swapped version of this.
-/
lemma symmDiff_subset_sdiff' : t \ s ⊆ s ∆ t := subset_union_right
/-
**Finset.symmDiff_subset_union** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：symmDiff_subset_union : s ∆ t subseteq s union t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_le_sup`：symmDiff_le_sup {a b : α} : a ∆ b <= a ⊔ b
-/
lemma symmDiff_subset_union : s ∆ t ⊆ s ∪ t := symmDiff_le_sup (α := Finset α)
/-
**Finset.symmDiff_eq_union_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：symmDiff_eq_union_iff (s t : Finset α) : s ∆ t = s union t ↔ Disjoint s t
参数：s t : Finset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_eq_sup`：symmDiff_eq_sup : a ∆ b = a ⊔ b ↔ Disjoint a b
-/
lemma symmDiff_eq_union_iff (s t : Finset α) : s ∆ t = s ∪ t ↔ Disjoint s t := symmDiff_eq_sup s t
/-
**Finset.symmDiff_eq_union** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：symmDiff_eq_union (h : Disjoint s t) : s ∆ t = s union t
参数：h : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.symmDiff_eq_sup`：Disjoint.symmDiff_eq_sup {a b : α} (h : Disjoi
nt a b) : a ∆ b = a ⊔ b
-/
lemma symmDiff_eq_union (h : Disjoint s t) : s ∆ t = s ∪ t := Disjoint.symmDiff_eq_sup h

end SymmDiff

end Finset

