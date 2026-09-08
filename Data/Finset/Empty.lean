/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Multiset.ZeroCons
public import Aesop

/-!
# Empty and nonempty finite sets

This file defines the empty finite set ∅ and a predicate for nonempty `Finset`s.

## Main declarations
* `Finset.Nonempty`: A finset is nonempty if it has elements. This is equivalent to saying `s ≠ ∅`.
* `Finset.empty`: Denoted by `∅`. The finset associated to any type consisting of no elements.

## Tags

finite sets, finset

-/

@[expose] public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice IsOrderedMonoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

/-! ### Nonempty -/


/-- The property `s.Nonempty` expresses the fact that the finset `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
/-
**Finset.Nonempty** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_1} → Finset α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property `s.Nonempty` expresses the fact that the finset `s` is not empty. I
t should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to 
a nice API thanks
to the dot notation.
-/
protected def Nonempty (s : Finset α) : Prop := ∃ x : α, x ∈ s

@[grind =]
/-
**Finset.nonempty_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：nonempty_def {s : Finset α} : s.Nonempty ↔ exists x, x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nonempty_def {s : Finset α} : s.Nonempty ↔ ∃ x, x ∈ s := Iff.rfl
/-
**Finset.decidableNonempty** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：decidableNonempty {s : Finset α} : Decidable s.Nonempty
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableNonempty {s : Finset α} : Decidable s.Nonempty :=
  decidable_of_iff (∃ a ∈ s, true) <| by simp [Finset.Nonempty]

@[simp, norm_cast]
/-
**Finset.coe_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_nonempty {s : Finset α} : (s : Set α).Nonempty ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_nonempty {s : Finset α} : (s : Set α).Nonempty ↔ s.Nonempty :=
  Iff.rfl

-- Not `@[simp]` since `nonempty_subtype` already is.
/-
**Finset.nonempty_coe_sort** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：nonempty_coe_sort {s : Finset α} : Nonempty (s : Type _) ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_subtype`：nonempty_subtype {α} {p : α -> Prop} : Nonempty (Subty
pe p) ↔ exists a : α, p a
-/
theorem nonempty_coe_sort {s : Finset α} : Nonempty (s : Type _) ↔ s.Nonempty :=
  nonempty_subtype

alias ⟨_, Nonempty.to_set⟩ := coe_nonempty

alias ⟨_, Nonempty.coe_sort⟩ := nonempty_coe_sort
/-
**Finset.Nonempty.exists_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → ∃ x, x ∈ s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Nonempty.exists_mem {s : Finset α} (h : s.Nonempty) : ∃ x : α, x ∈ s :=
  h
/-
**Finset.Nonempty.mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_1} {s t : Finset α}, s ⊆ t → s.Nonempty → t.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
-/
@[gcongr] theorem Nonempty.mono {s t : Finset α} (hst : s ⊆ t) (hs : s.Nonempty) : t.Nonempty :=
  Set.Nonempty.mono hst hs
/-
**Finset.Nonempty.forall_const** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → ∀ {p : Prop}, (∀ x ∈ s, p) ↔
 p
参数：∀ x ∈ s, p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Nonempty.forall_const {s : Finset α} (h : s.Nonempty) {p : Prop} : (∀ x ∈ s, p) ↔ p :=
  let ⟨x, hx⟩ := h
  ⟨fun h => h x hx, fun h _ _ => h⟩

@[simp]
/-
**Finset.forall_mem_const** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：forall_mem_const {s : Finset α} [Nonempty s] {p : Prop} : (forall x in s, 
p) ↔ p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.forall_const`：∀ {α : Type u_1} {s : Finset α}, s.Nonempt
y → ∀ {p : Prop}, (∀ x ∈ s, p) ↔ p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.nonempty_coe_sort`：nonempty_coe_sort {s : Finset α} : Nonempty (s
 : Type _) ↔ s.Nonempty
-/
theorem forall_mem_const {s : Finset α} [Nonempty s] {p : Prop} : (∀ x ∈ s, p) ↔ p :=
  (nonempty_coe_sort.mp ‹_›).forall_const
/-
**Finset.Nonempty.to_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → Nonempty ↥s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.nonempty_coe_sort`：nonempty_coe_sort {s : Finset α} : Nonempty (s
 : Type _) ↔ s.Nonempty
-/
theorem Nonempty.to_subtype {s : Finset α} : s.Nonempty → Nonempty s :=
  nonempty_coe_sort.2
/-
**Finset.Nonempty.to_type** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → Nonempty α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Nonempty.to_type {s : Finset α} : s.Nonempty → Nonempty α := fun ⟨x, _hx⟩ => ⟨x⟩

/-! ### empty -/


section Empty

variable {s : Finset α}

/-- The empty finset -/
/-
**Finset.empty** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_1} → Finset α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.nodup_zero`：nodup_zero : @Nodup α 0

--- 原说明 ---
The empty finset
-/
protected def empty : Finset α :=
  ⟨0, nodup_zero⟩
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EmptyCollection (Finset α) :=
  ⟨Finset.empty⟩
/-
**Finset.inhabitedFinset** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：inhabitedFinset : Inhabited (Finset α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedFinset : Inhabited (Finset α) :=
  ⟨∅⟩

@[simp]
/-
**Finset.empty_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：empty_val : (∅ : Finset α).1 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem empty_val : (∅ : Finset α).1 = 0 :=
  rfl

@[simp, grind ←]
/-
**Finset.notMem_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：notMem_empty (a : α) : a ∉ (∅ : Finset α)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem notMem_empty (a : α) : a ∉ (∅ : Finset α) := by
  simp only [mem_def, empty_val, notMem_zero, not_false_iff]

@[simp]
/-
**Finset.not_nonempty_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：not_nonempty_empty : ¬(∅ : Finset α).Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.notMem_empty`：notMem_empty (a : α) : a ∉ (∅ : Finset α)
-/
theorem not_nonempty_empty : ¬(∅ : Finset α).Nonempty := fun ⟨x, hx⟩ => notMem_empty x hx

@[simp]
/-
**Finset.mk_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mk_zero : (⟨0, nodup_zero⟩ : Finset α) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.nodup_zero`：nodup_zero : @Nodup α 0
-/
theorem mk_zero : (⟨0, nodup_zero⟩ : Finset α) = ∅ :=
  rfl
/-
**Finset.ne_empty_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ne_empty_of_mem {a : α} {s : Finset α} (h : a in s) : s != ∅
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.notMem_empty`：notMem_empty (a : α) : a ∉ (∅ : Finset α)
-/
theorem ne_empty_of_mem {a : α} {s : Finset α} (h : a ∈ s) : s ≠ ∅ := fun e =>
  notMem_empty a <| e ▸ h
/-
**Finset.Nonempty.ne_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → s ≠ ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Finset.ne_empty_of_mem`：ne_empty_of_mem {a : α} {s : Finset α} (h : a in
 s) : s != ∅
-/
theorem Nonempty.ne_empty {s : Finset α} (h : s.Nonempty) : s ≠ ∅ :=
  (Exists.elim h) fun _a => ne_empty_of_mem

@[simp]
/-
**Finset.empty_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：empty_subset (s : Finset α) : ∅ subseteq s
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.zero_subset`：zero_subset (s : Multiset α) : 0 subseteq s
-/
theorem empty_subset (s : Finset α) : ∅ ⊆ s :=
  zero_subset _
/-
**Finset.eq_empty_of_forall_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_empty_of_forall_notMem {s : Finset α} (H : forall x, x ∉ s) : s = ∅
参数：H : forall x, x ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Multiset.eq_zero_of_forall_notMem`：eq_zero_of_forall_notMem {s : Multise
t α} : (forall x, x ∉ s) -> s = 0
-/
theorem eq_empty_of_forall_notMem {s : Finset α} (H : ∀ x, x ∉ s) : s = ∅ :=
  eq_of_veq (eq_zero_of_forall_notMem H)
/-
**Finset.eq_empty_iff_forall_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_empty_iff_forall_notMem {s : Finset α} : s = ∅ ↔ forall x, x ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_empty_iff_forall_notMem {s : Finset α} : s = ∅ ↔ ∀ x, x ∉ s := by grind

@[simp]
/-
**Finset.val_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：val_eq_zero {s : Finset α} : s.1 = 0 ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.val_inj`：val_inj {s t : Finset α} : s.1 = t.1 ↔ s = t
-/
theorem val_eq_zero {s : Finset α} : s.1 = 0 ↔ s = ∅ :=
  @val_inj _ s ∅
/-
**Finset.subset_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {s : Finset α}, s ⊆ ∅ ↔ s = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Multiset.subset_zero`：∀ {α : Type u_1} {s : Multiset α}, s ⊆ 0 ↔ s = 0
· 使用定理 `Finset.val_eq_zero`：val_eq_zero {s : Finset α} : s.1 = 0 ↔ s = ∅
-/
@[simp] lemma subset_empty : s ⊆ ∅ ↔ s = ∅ := subset_zero.trans val_eq_zero

@[simp]
/-
**Finset.not_ssubset_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：not_ssubset_empty (s : Finset α) : ¬s ⊂ ∅
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem not_ssubset_empty (s : Finset α) : ¬s ⊂ ∅ := by grind
/-
**Finset.nonempty_of_ne_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：nonempty_of_ne_empty {s : Finset α} (h : s != ∅) : s.Nonempty
参数：h : s != ∅。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.exists_mem_of_ne_zero`：exists_mem_of_ne_zero {s : Multiset α} :
 s != 0 -> exists a : α, a in s
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.val_eq_zero`：val_eq_zero {s : Finset α} : s.1 = 0 ↔ s = ∅
-/
theorem nonempty_of_ne_empty {s : Finset α} (h : s ≠ ∅) : s.Nonempty :=
  exists_mem_of_ne_zero (mt val_eq_zero.1 h)

@[push ←]
/-
**Finset.nonempty_iff_ne_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：nonempty_iff_ne_empty {s : Finset α} : s.Nonempty ↔ s != ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.ne_empty`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
s ≠ ∅
· 使用定理 `Finset.nonempty_of_ne_empty`：nonempty_of_ne_empty {s : Finset α} (h : s 
!= ∅) : s.Nonempty
-/
theorem nonempty_iff_ne_empty {s : Finset α} : s.Nonempty ↔ s ≠ ∅ :=
  ⟨Nonempty.ne_empty, nonempty_of_ne_empty⟩

@[simp, push]
/-
**Finset.not_nonempty_iff_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：not_nonempty_iff_eq_empty {s : Finset α} : ¬s.Nonempty ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
-/
theorem not_nonempty_iff_eq_empty {s : Finset α} : ¬s.Nonempty ↔ s = ∅ :=
  nonempty_iff_ne_empty.not.trans not_not
/-
**Finset.eq_empty_or_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_empty_or_nonempty (s : Finset α) : s = ∅ ∨ s.Nonempty
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_cases`：by_cases {p q : Prop} (hpq : p -> q) (hnpq : ¬p -> q) : q
· 使用定理 `Finset.nonempty_of_ne_empty`：nonempty_of_ne_empty {s : Finset α} (h : s 
!= ∅) : s.Nonempty
-/
theorem eq_empty_or_nonempty (s : Finset α) : s = ∅ ∨ s.Nonempty :=
  by_cases Or.inl fun h => Or.inr (nonempty_of_ne_empty h)

@[simp, norm_cast]
/-
**Finset.coe_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_empty : ((∅ : Finset α) : Set α) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_empty : ((∅ : Finset α) : Set α) = ∅ := by grind

@[simp, norm_cast]
/-
**Finset.coe_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_eq_empty {s : Finset α} : (s : Set α) = ∅ ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_eq_empty {s : Finset α} : (s : Set α) = ∅ ↔ s = ∅ := by grind

@[simp]
/-
**Finset.isEmpty_coe_sort** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：isEmpty_coe_sort {s : Finset α} : IsEmpty (s : Type _) ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.isEmpty_coe_sort`：isEmpty_coe_sort {s : Set α} : IsEmpty (↥s) ↔ s = 
∅
-/
theorem isEmpty_coe_sort {s : Finset α} : IsEmpty (s : Type _) ↔ s = ∅ := by
  simpa using @Set.isEmpty_coe_sort α s
/-
**Finset.instIsEmpty** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
形式化陈述：instIsEmpty : IsEmpty (∅ : Finset α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.isEmpty_coe_sort`：isEmpty_coe_sort {s : Finset α} : IsEmpty (s : 
Type _) ↔ s = ∅
-/
instance instIsEmpty : IsEmpty (∅ : Finset α) :=
  isEmpty_coe_sort.2 rfl

/-- A `Finset` for an empty type is empty. -/
/-
**Finset.eq_empty_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_empty_of_isEmpty [IsEmpty α] (s : Finset α) : s = ∅
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_of_forall_notMem`：eq_empty_of_forall_notMem {s : Finset 
α} (H : forall x, x ∉ s) : s = ∅

--- 原说明 ---
A `Finset` for an empty type is empty.
-/
theorem eq_empty_of_isEmpty [IsEmpty α] (s : Finset α) : s = ∅ :=
  Finset.eq_empty_of_forall_notMem isEmptyElim
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderBot (Finset α) where
  bot := ∅
  bot_le := empty_subset

@[simp, grind =]
/-
**Finset.bot_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：bot_eq_empty : (⊥ : Finset α) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_eq_empty : (⊥ : Finset α) = ∅ :=
  rfl

@[simp]
/-
**Finset.empty_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：empty_ssubset : ∅ ⊂ s ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
-/
theorem empty_ssubset : ∅ ⊂ s ↔ s.Nonempty :=
  (@bot_lt_iff_ne_bot (Finset α) _ _ _).trans nonempty_iff_ne_empty.symm

alias ⟨_, Nonempty.empty_ssubset⟩ := empty_ssubset

-- useful rules for calculations with quantifiers
/-
**Finset.exists_mem_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：exists_mem_empty_iff (p : α -> Prop) : (exists x, x in (∅ : Finset α) ∧ p 
x) ↔ False
参数：p : α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_mem_empty_iff (p : α → Prop) : (∃ x, x ∈ (∅ : Finset α) ∧ p x) ↔ False := by
  grind
/-
**Finset.forall_mem_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：forall_mem_empty_iff (p : α -> Prop) : (forall x, x in (∅ : Finset α) -> p
 x) ↔ True
参数：p : α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall_mem_empty_iff (p : α → Prop) : (∀ x, x ∈ (∅ : Finset α) → p x) ↔ True := by
  grind

end Empty
end Finset

namespace Mathlib.Meta
open Qq Lean Meta Finset

/-- Attempt to prove that a finset is nonempty using the `finsetNonempty` aesop rule-set.

You can add lemmas to the rule-set by tagging them with either:
* `aesop safe apply (rule_sets := [finsetNonempty])` if they are always a good idea to follow or
* `aesop unsafe apply (rule_sets := [finsetNonempty])` if they risk directing the search to a blind
  alley.

TODO: should some of the lemmas be `aesop safe simp` instead?
-/
meta def proveFinsetNonempty {u : Level} {α : Q(Type u)} (s : Q(Finset $α)) :
    MetaM (Option Q(Finset.Nonempty $s)) := do
  -- Aesop expects to operate on goals, so we're going to make a new goal.
  let goal ← Lean.Meta.mkFreshExprMVar q(Finset.Nonempty $s)
  let mvar := goal.mvarId!
  -- We want this to be fast, so use only the basic and `Finset.Nonempty`-specific rules.
  let rulesets ← Aesop.Frontend.getGlobalRuleSets #[`builtin, `finsetNonempty]
  let options : Aesop.Options' :=
    { terminal := true -- Fail if the new goal is not closed.
      generateScript := false
      useDefaultSimpSet := false -- Avoiding the whole simp set to speed up the tactic.
      warnOnNonterminal := false -- Don't show a warning on failure, simply return `none`.
      forwardMaxDepth? := none }
  let rules ← Aesop.mkLocalRuleSet rulesets options
  let (remainingGoals, _) ←
    try Aesop.search (options := options.toOptions) mvar (.some rules)
    catch _ => return none
  -- Fail if there are open goals remaining, this serves as an extra check for the
  -- Aesop configuration option `terminal := true`.
  if remainingGoals.size > 0 then return none
  Lean.getExprMVarAssignment? mvar

end Mathlib.Meta

