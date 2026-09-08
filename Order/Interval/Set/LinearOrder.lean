/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
-/
module

public import Mathlib.Order.Interval.Set.Basic

/-!
# Interval properties in linear orders

Since every pair of elements are comparable in a linear order, intervals over them are
better behaved. This file collects their properties under this assumption.
-/

public section

assert_not_exists RelIso

open Function

namespace Set

variable {α : Type*} [LinearOrder α] {a a₁ a₂ b b₁ b₂ c d : α}

@[to_dual]
/-
**Set.notMem_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：notMem_Ici : c ∉ Ici a ↔ c < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
-/
theorem notMem_Ici : c ∉ Ici a ↔ c < a :=
  not_le

@[to_dual]
/-
**Set.notMem_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：notMem_Ioi : c ∉ Ioi a ↔ c <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
-/
theorem notMem_Ioi : c ∉ Ioi a ↔ c ≤ a :=
  not_lt

@[to_dual (attr := simp)]
/-
**Set.compl_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_Iic : (Iic a)ᶜ = Ioi a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
-/
theorem compl_Iic : (Iic a)ᶜ = Ioi a :=
  ext fun _ => not_le

@[to_dual (attr := simp)]
/-
**Set.compl_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_Iio : (Iio a)ᶜ = Ici a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
-/
theorem compl_Iio : (Iio a)ᶜ = Ici a :=
  ext fun _ => not_lt

@[to_dual (attr := simp)]
/-
**Set.Ici_sdiff_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ici_sdiff_Ici : Ici a \ Ici b = Ico a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Set.compl_Ici`：∀ {α : Type u_1} [inst : LinearOrder α] {a : α}, (Set.Ici
 a)ᶜ = Set.Iio a
· 使用定理 `Set.Ici_inter_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
ci a ∩ Set.Iio b = Set.Ico a b
-/
theorem Ici_sdiff_Ici : Ici a \ Ici b = Ico a b := by rw [sdiff_eq, compl_Ici, Ici_inter_Iio]

@[deprecated (since := "2026-06-03")] alias Ici_diff_Ici := Ici_sdiff_Ici

@[to_dual (attr := simp)]
/-
**Set.Ici_sdiff_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ici_sdiff_Ioi : Ici a \ Ioi b = Icc a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Set.compl_Ioi`：∀ {α : Type u_1} [inst : LinearOrder α] {a : α}, (Set.Ioi
 a)ᶜ = Set.Iic a
· 使用定理 `Set.Ici_inter_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
ci a ∩ Set.Iic b = Set.Icc a b
-/
theorem Ici_sdiff_Ioi : Ici a \ Ioi b = Icc a b := by rw [sdiff_eq, compl_Ioi, Ici_inter_Iic]

@[deprecated (since := "2026-06-03")] alias Ici_diff_Ioi := Ici_sdiff_Ioi

@[to_dual (attr := simp)]
/-
**Set.Ioi_sdiff_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioi_sdiff_Ioi : Ioi a \ Ioi b = Ioc a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Set.compl_Ioi`：∀ {α : Type u_1} [inst : LinearOrder α] {a : α}, (Set.Ioi
 a)ᶜ = Set.Iic a
· 使用定理 `Set.Ioi_inter_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
oi a ∩ Set.Iic b = Set.Ioc a b
-/
theorem Ioi_sdiff_Ioi : Ioi a \ Ioi b = Ioc a b := by rw [sdiff_eq, compl_Ioi, Ioi_inter_Iic]

@[deprecated (since := "2026-06-03")] alias Ioi_diff_Ioi := Ioi_sdiff_Ioi

@[to_dual (attr := simp)]
/-
**Set.Ioi_sdiff_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioi_sdiff_Ici : Ioi a \ Ici b = Ioo a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `Set.compl_Ici`：∀ {α : Type u_1} [inst : LinearOrder α] {a : α}, (Set.Ici
 a)ᶜ = Set.Iio a
· 使用定理 `Set.Ioi_inter_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
oi a ∩ Set.Iio b = Set.Ioo a b
-/
theorem Ioi_sdiff_Ici : Ioi a \ Ici b = Ioo a b := by rw [sdiff_eq, compl_Ici, Ioi_inter_Iio]

@[deprecated (since := "2026-06-03")] alias Ioi_diff_Ici := Ioi_sdiff_Ici

@[to_dual]
/-
**Set.Ioi_injective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioi_injective : Injective (Ioi : α -> Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_gt_iff`：∀ {α : Type u_2} [inst : LinearOrder α] {a b : α}, 
(∀ (c : α), a < c ↔ b < c) → a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
-/
theorem Ioi_injective : Injective (Ioi : α → Set α) := fun _ _ =>
  eq_of_forall_gt_iff ∘ Set.ext_iff.1

@[to_dual]
/-
**Set.Ioi_inj** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioi_inj : Ioi a = Ioi b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Set.Ioi_injective`：Ioi_injective : Injective (Ioi : α -> Set α)
-/
theorem Ioi_inj : Ioi a = Ioi b ↔ a = b :=
  Ioi_injective.eq_iff
/-
**Set.Ico_subset_Ico_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_subset_Ico_iff (h₁ : a₁ < b₁) : Ico a₁ b₁ subseteq Ico a₂ b₂ ↔ a₂ <= a
₁ ∧ b₁ <= b₂
参数：h₁ : a₁ < b₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.Ico_subset_Ico`：Ico_subset_Ico (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ico
 a₁ b₁ subseteq Ico a₂ b₂
-/
theorem Ico_subset_Ico_iff (h₁ : a₁ < b₁) : Ico a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
  ⟨fun h =>
    have : a₂ ≤ a₁ ∧ a₁ < b₂ := h ⟨le_rfl, h₁⟩
    ⟨this.1, le_of_not_gt fun h' => lt_irrefl b₂ (h ⟨this.2.le, h'⟩).2⟩,
    fun ⟨h₁, h₂⟩ => Ico_subset_Ico h₁ h₂⟩
/-
**Set.Ioc_subset_Ioc_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_subset_Ioc_iff (h₁ : a₁ < b₁) : Ioc a₁ b₁ subseteq Ioc a₂ b₂ ↔ b₁ <= b
₂ ∧ a₂ <= a₁
参数：h₁ : a₁ < b₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.Ico_toDual`：Ico_toDual : Ico (toDual a) (toDual b) = ofDual ⁻¹' Ioc 
b a
· 使用定理 `Set.Ico_subset_Ico_iff`：Ico_subset_Ico_iff (h₁ : a₁ < b₁) : Ico a₁ b₁ su
bseteq Ico a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ <= b₂
-/
theorem Ioc_subset_Ioc_iff (h₁ : a₁ < b₁) : Ioc a₁ b₁ ⊆ Ioc a₂ b₂ ↔ b₁ ≤ b₂ ∧ a₂ ≤ a₁ := by
  convert! @Ico_subset_Ico_iff αᵒᵈ _ b₁ b₂ a₁ a₂ h₁ using 2 <;> exact (@Ico_toDual α _ _ _).symm
/-
**Set.Ico_eq_Ico_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_eq_Ico_iff (h : a < b ∨ c < d) : Ico a b = Ico c d ↔ a = c ∧ b = d
参数：h : a < b ∨ c < d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.Ico_subset_Ico_iff`：Ico_subset_Ico_iff (h₁ : a₁ < b₁) : Ico a₁ b₁ su
bseteq Ico a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ <= b₂
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.superset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preord
er α] {a b : α}, a = b → b ⊆ a
-/
theorem Ico_eq_Ico_iff (h : a < b ∨ c < d) : Ico a b = Ico c d ↔ a = c ∧ b = d := by
  refine ⟨fun h ↦ ?_, by grind⟩
  have : c ≤ a ∧ b ≤ d := (Ico_subset_Ico_iff (show a < b by grind [Set.nonempty_Ico])).1 h.subset
  have : a ≤ c ∧ d ≤ b := (Ico_subset_Ico_iff (show c < d by grind)).1 h.superset
  grind
/-
**Set.Ioc_eq_Ioc_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_eq_Ioc_iff (hab : a < b ∨ c < d) : Ioc a b = Ioc c d ↔ a = c ∧ b = d
参数：hab : a < b ∨ c < d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.Ioc_subset_Ioc_iff`：Ioc_subset_Ioc_iff (h₁ : a₁ < b₁) : Ioc a₁ b₁ su
bseteq Ioc a₂ b₂ ↔ b₁ <= b₂ ∧ a₂ <= a₁
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.superset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preord
er α] {a b : α}, a = b → b ⊆ a
-/
theorem Ioc_eq_Ioc_iff (hab : a < b ∨ c < d) : Ioc a b = Ioc c d ↔ a = c ∧ b = d := by
  refine ⟨fun h ↦ ?_, by grind⟩
  have : b ≤ d ∧ c ≤ a := (Ioc_subset_Ioc_iff (show a < b by grind [Set.nonempty_Ioc])).1 h.subset
  have : d ≤ b ∧ a ≤ c := (Ioc_subset_Ioc_iff (show c < d by grind)).1 h.superset
  grind
/-
**Set.Ioo_subset_Ioo_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_subset_Ioo_iff [DenselyOrdered α] (h₁ : a₁ < b₁) : Ioo a₁ b₁ subseteq 
Ioo a₂ b₂ ↔ a₂ <= a₁ ∧ b₁ <= b₂
参数：h₁ : a₁ < b₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Ioo_subset_Ioo`：Ioo_subset_Ioo (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ioo
 a₁ b₁ subseteq Ioo a₂ b₂
-/
theorem Ioo_subset_Ioo_iff [DenselyOrdered α] (h₁ : a₁ < b₁) :
    Ioo a₁ b₁ ⊆ Ioo a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
  ⟨fun h => by
    rcases exists_between h₁ with ⟨x, xa, xb⟩
    constructor <;> refine le_of_not_gt fun h' => ?_
    · have ab := (h ⟨xa, xb⟩).1.trans xb
      exact lt_irrefl _ (h ⟨h', ab⟩).1
    · have ab := xa.trans (h ⟨xa, xb⟩).2
      exact lt_irrefl _ (h ⟨ab, h'⟩).2,
    fun ⟨h₁, h₂⟩ => Ioo_subset_Ioo h₁ h₂⟩

@[to_dual]
/-
**Set.Ici_eq_singleton_iff_isTop** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ici_eq_singleton_iff_isTop {x : α} : (Ici x = {x}) ↔ IsTop x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LE.le.ge_iff_eq`：ge_iff_eq (h : a <= b) : b <= a ↔ a = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Ici_eq_singleton_iff_isTop {x : α} : (Ici x = {x}) ↔ IsTop x := by
  refine ⟨fun h y ↦ ?_, fun h ↦ by ext y; simp [(h y).ge_iff_eq]⟩
  by_contra! H
  have : y ∈ Ici x := H.le
  rw [h, mem_singleton_iff] at this
  exact lt_irrefl y (this.le.trans_lt H)

@[to_dual (attr := simp)]
/-
**Set.Ioi_subset_Ioi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioi_subset_Ioi_iff : Ioi b subseteq Ioi a ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Set.Ioi_subset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ≤ 
a → Set.Ioi a ⊆ Set.Ioi b
-/
theorem Ioi_subset_Ioi_iff : Ioi b ⊆ Ioi a ↔ a ≤ b := by
  refine ⟨fun h => ?_, Ioi_subset_Ioi⟩
  by_contra ba
  exact lt_irrefl _ (h (not_le.mp ba))

@[to_dual (attr := simp)]
/-
**Set.Ioi_ssubset_Ioi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioi_ssubset_Ioi_iff : Ioi b ⊂ Ioi a ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ssubset_iff_exists`：ssubset_iff_exists {s t : Set α} : s ⊂ t ↔ s sub
seteq t ∧ exists x in t, x ∉ s
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Set.Ioi_ssubset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b <
 a → Set.Ioi a ⊂ Set.Ioi b
-/
theorem Ioi_ssubset_Ioi_iff : Ioi b ⊂ Ioi a ↔ a < b := by
  refine ⟨fun h => ?_, Ioi_ssubset_Ioi⟩
  obtain ⟨_, c, ac, cb⟩ := ssubset_iff_exists.mp h
  exact ac.trans_le (le_of_not_gt cb)

@[to_dual (attr := simp)]
/-
**Set.Ioi_subset_Ici_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioi_subset_Ici_iff [DenselyOrdered α] : Ioi b subseteq Ici a ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Set.Ioi_subset_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ≤ 
a → Set.Ioi a ⊆ Set.Ici b
-/
theorem Ioi_subset_Ici_iff [DenselyOrdered α] : Ioi b ⊆ Ici a ↔ a ≤ b := by
  refine ⟨fun h => ?_, Ioi_subset_Ici⟩
  by_contra ba
  obtain ⟨c, bc, ca⟩ : ∃ c, b < c ∧ c < a := exists_between (not_le.mp ba)
  exact lt_irrefl _ (ca.trans_le (h bc))

/-! ### Two infinite intervals -/

@[to_dual]
/-
**Set.Iic_union_Ioi_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_union_Ioi_of_le (h : a <= b) : Iic b union Ioi a = univ
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用引理 `LE.le.gt_or_le`：gt_or_le (h : a <= b) (c : α) : a < c ∨ c <= b

--- 原说明 ---
### Two infinite intervals
-/
theorem Iic_union_Ioi_of_le (h : a ≤ b) : Iic b ∪ Ioi a = univ :=
  eq_univ_of_forall fun x => (h.gt_or_le x).symm

@[to_dual]
/-
**Set.Iio_union_Ici_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_union_Ici_of_le (h : a <= b) : Iio b union Ici a = univ
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用引理 `LE.le.ge_or_lt`：ge_or_lt (h : a <= b) (c : α) : a <= c ∨ c < b
-/
theorem Iio_union_Ici_of_le (h : a ≤ b) : Iio b ∪ Ici a = univ :=
  eq_univ_of_forall fun x => (h.ge_or_lt x).symm

@[to_dual]
/-
**Set.Iic_union_Ici_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_union_Ici_of_le (h : a <= b) : Iic b union Ici a = univ
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用引理 `LE.le.ge_or_le`：ge_or_le (h : a <= b) (c : α) : a <= c ∨ c <= b
-/
theorem Iic_union_Ici_of_le (h : a ≤ b) : Iic b ∪ Ici a = univ :=
  eq_univ_of_forall fun x => (h.ge_or_le x).symm

@[to_dual]
/-
**Set.Iio_union_Ioi_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_union_Ioi_of_lt (h : a < b) : Iio b union Ioi a = univ
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用引理 `LT.lt.gt_or_lt`：gt_or_lt (h : a < b) (c : α) : a < c ∨ c < b
-/
theorem Iio_union_Ioi_of_lt (h : a < b) : Iio b ∪ Ioi a = univ :=
  eq_univ_of_forall fun x => (h.gt_or_lt x).symm

@[to_dual (attr := simp)]
/-
**Set.Iic_union_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_union_Ici : Iic a union Ici a = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Iic_union_Ici_of_le`：Iic_union_Ici_of_le (h : a <= b) : Iic b union 
Ici a = univ
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Iic_union_Ici : Iic a ∪ Ici a = univ :=
  Iic_union_Ici_of_le le_rfl

@[to_dual (attr := simp)]
/-
**Set.Iio_union_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_union_Ici : Iio a union Ici a = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Iio_union_Ici_of_le`：Iio_union_Ici_of_le (h : a <= b) : Iio b union 
Ici a = univ
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Iio_union_Ici : Iio a ∪ Ici a = univ :=
  Iio_union_Ici_of_le le_rfl

@[to_dual (attr := simp)]
/-
**Set.Iic_union_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_union_Ioi : Iic a union Ioi a = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Iic_union_Ioi_of_le`：Iic_union_Ioi_of_le (h : a <= b) : Iic b union 
Ioi a = univ
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Iic_union_Ioi : Iic a ∪ Ioi a = univ :=
  Iic_union_Ioi_of_le le_rfl

@[to_dual (attr := simp)]
/-
**Set.Iio_union_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_union_Ioi : Iio a union Ioi a = {a}ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `lt_or_lt_iff_ne`：lt_or_lt_iff_ne : a < b ∨ b < a ↔ a != b
-/
theorem Iio_union_Ioi : Iio a ∪ Ioi a = {a}ᶜ :=
  ext fun _ => lt_or_lt_iff_ne

/-! ### A finite and an infinite interval -/

/-
**Set.Ioo_union_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_union_Ioi (h : c < max a b) : Ioo a b union Ioi c = Ioi (min a c)
参数：h : c < max a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### A finite and an infinite interval
-/
theorem Ioo_union_Ioi (h : c < max a b) : Ioo a b ∪ Ioi c = Ioi (min a c) := by
  grind

@[deprecated Ioo_union_Ioi (since := "2026-02-22")]
/-
**Set.Ioo_union_Ioi'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_union_Ioi' (h₁ : c < b) : Ioo a b union Ioi c = Ioi (min a c)
参数：h₁ : c < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioo_union_Ioi`：Ioo_union_Ioi (h : c < max a b) : Ioo a b union Ioi c
 = Ioi (min a c)
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem Ioo_union_Ioi' (h₁ : c < b) : Ioo a b ∪ Ioi c = Ioi (min a c) :=
  Ioo_union_Ioi (h₁.trans_le (le_max_right ..))
/-
**Set.Ioi_subset_Ioo_union_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioi_subset_Ioo_union_Ici : Ioi a subseteq Ioo a b union Ici b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
-/
theorem Ioi_subset_Ioo_union_Ici : Ioi a ⊆ Ioo a b ∪ Ici b := fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb

@[simp]
/-
**Set.Ioo_union_Ici_eq_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_union_Ici_eq_Ioi (h : a < b) : Ioo a b union Ici b = Ioi a
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Set.Ioi_subset_Ioo_union_Ici`：Ioi_subset_Ioo_union_Ici : Ioi a subseteq 
Ioo a b union Ici b
-/
theorem Ioo_union_Ici_eq_Ioi (h : a < b) : Ioo a b ∪ Ici b = Ioi a :=
  Subset.antisymm (fun _ hx => hx.elim And.left h.trans_le) Ioi_subset_Ioo_union_Ici
/-
**Set.Ici_subset_Ico_union_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ici_subset_Ico_union_Ici : Ici a subseteq Ico a b union Ici b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
-/
theorem Ici_subset_Ico_union_Ici : Ici a ⊆ Ico a b ∪ Ici b := fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb

@[simp]
/-
**Set.Ico_union_Ici_eq_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_union_Ici_eq_Ici (h : a <= b) : Ico a b union Ici b = Ici a
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ici_subset_Ico_union_Ici`：Ici_subset_Ico_union_Ici : Ici a subseteq 
Ico a b union Ici b
-/
theorem Ico_union_Ici_eq_Ici (h : a ≤ b) : Ico a b ∪ Ici b = Ici a :=
  Subset.antisymm (fun _ hx => hx.elim And.left h.trans) Ici_subset_Ico_union_Ici
/-
**Set.Ico_union_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_union_Ici (h : c <= max a b) : Ico a b union Ici c = Ici (min a c)
参数：h : c <= max a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ico_union_Ici (h : c ≤ max a b) : Ico a b ∪ Ici c = Ici (min a c) := by
  grind

@[deprecated Ico_union_Ici (since := "2026-02-22")]
/-
**Set.Ico_union_Ici'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_union_Ici' (h₁ : c <= b) : Ico a b union Ici c = Ici (min a c)
参数：h₁ : c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ico_union_Ici`：Ico_union_Ici (h : c <= max a b) : Ico a b union Ici 
c = Ici (min a c)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem Ico_union_Ici' (h₁ : c ≤ b) : Ico a b ∪ Ici c = Ici (min a c) :=
  Ico_union_Ici (h₁.trans (le_max_right ..))
/-
**Set.Ioi_subset_Ioc_union_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioi_subset_Ioc_union_Ioi : Ioi a subseteq Ioc a b union Ioi b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
-/
theorem Ioi_subset_Ioc_union_Ioi : Ioi a ⊆ Ioc a b ∪ Ioi b := fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb

@[simp]
/-
**Set.Ioc_union_Ioi_eq_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_union_Ioi_eq_Ioi (h : a <= b) : Ioc a b union Ioi b = Ioi a
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Set.Ioi_subset_Ioc_union_Ioi`：Ioi_subset_Ioc_union_Ioi : Ioi a subseteq 
Ioc a b union Ioi b
-/
theorem Ioc_union_Ioi_eq_Ioi (h : a ≤ b) : Ioc a b ∪ Ioi b = Ioi a :=
  Subset.antisymm (fun _ hx => hx.elim And.left h.trans_lt) Ioi_subset_Ioc_union_Ioi
/-
**Set.Ioc_union_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_union_Ioi (h : c <= max a b) : Ioc a b union Ioi c = Ioi (min a c)
参数：h : c <= max a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioc_union_Ioi (h : c ≤ max a b) : Ioc a b ∪ Ioi c = Ioi (min a c) := by
  grind

@[deprecated Ioc_union_Ioi (since := "2026-02-22")]
/-
**Set.Ioc_union_Ioi'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_union_Ioi' (h₁ : c <= b) : Ioc a b union Ioi c = Ioi (min a c)
参数：h₁ : c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioc_union_Ioi`：Ioc_union_Ioi (h : c <= max a b) : Ioc a b union Ioi 
c = Ioi (min a c)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem Ioc_union_Ioi' (h₁ : c ≤ b) : Ioc a b ∪ Ioi c = Ioi (min a c) :=
  Ioc_union_Ioi (h₁.trans (le_max_right ..))
/-
**Set.Ici_subset_Icc_union_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ici_subset_Icc_union_Ioi : Ici a subseteq Icc a b union Ioi b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
-/
theorem Ici_subset_Icc_union_Ioi : Ici a ⊆ Icc a b ∪ Ioi b := fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx, hxb⟩) fun hxb => Or.inr hxb

@[simp]
/-
**Set.Icc_union_Ioi_eq_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_union_Ioi_eq_Ici (h : a <= b) : Icc a b union Ioi b = Ici a
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.Ici_subset_Icc_union_Ioi`：Ici_subset_Icc_union_Ioi : Ici a subseteq 
Icc a b union Ioi b
-/
theorem Icc_union_Ioi_eq_Ici (h : a ≤ b) : Icc a b ∪ Ioi b = Ici a :=
  Subset.antisymm (fun _ hx => (hx.elim And.left) fun hx' => h.trans <| le_of_lt hx')
    Ici_subset_Icc_union_Ioi
/-
**Set.Ioi_subset_Ioc_union_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioi_subset_Ioc_union_Ici : Ioi a subseteq Ioc a b union Ici b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.Ioi_subset_Ioo_union_Ici`：Ioi_subset_Ioo_union_Ici : Ioi a subseteq 
Ioo a b union Ici b
· 使用定理 `Set.union_subset_union_left`：union_subset_union_left {s₁ s₂ : Set α} (t)
 (h : s₁ subseteq s₂) : s₁ union t subseteq s₂ union t
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a
-/
theorem Ioi_subset_Ioc_union_Ici : Ioi a ⊆ Ioc a b ∪ Ici b :=
  Subset.trans Ioi_subset_Ioo_union_Ici (union_subset_union_left _ Ioo_subset_Ioc_self)

@[simp]
/-
**Set.Ioc_union_Ici_eq_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_union_Ici_eq_Ioi (h : a < b) : Ioc a b union Ici b = Ioi a
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Set.Ioi_subset_Ioc_union_Ici`：Ioi_subset_Ioc_union_Ici : Ioi a subseteq 
Ioc a b union Ici b
-/
theorem Ioc_union_Ici_eq_Ioi (h : a < b) : Ioc a b ∪ Ici b = Ioi a :=
  Subset.antisymm (fun _ hx => hx.elim And.left h.trans_le) Ioi_subset_Ioc_union_Ici
/-
**Set.Ici_subset_Icc_union_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ici_subset_Icc_union_Ici : Ici a subseteq Icc a b union Ici b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.Ici_subset_Ico_union_Ici`：Ici_subset_Ico_union_Ici : Ici a subseteq 
Ico a b union Ici b
· 使用定理 `Set.union_subset_union_left`：union_subset_union_left {s₁ s₂ : Set α} (t)
 (h : s₁ subseteq s₂) : s₁ union t subseteq s₂ union t
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
-/
theorem Ici_subset_Icc_union_Ici : Ici a ⊆ Icc a b ∪ Ici b :=
  Subset.trans Ici_subset_Ico_union_Ici (union_subset_union_left _ Ico_subset_Icc_self)

@[simp]
/-
**Set.Icc_union_Ici_eq_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_union_Ici_eq_Ici (h : a <= b) : Icc a b union Ici b = Ici a
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ici_subset_Icc_union_Ici`：Ici_subset_Icc_union_Ici : Ici a subseteq 
Icc a b union Ici b
-/
theorem Icc_union_Ici_eq_Ici (h : a ≤ b) : Icc a b ∪ Ici b = Ici a :=
  Subset.antisymm (fun _ hx => hx.elim And.left h.trans) Ici_subset_Icc_union_Ici
/-
**Set.Icc_union_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_union_Ici (h : c <= max a b) : Icc a b union Ici c = Ici (min a c)
参数：h : c <= max a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Icc_union_Ici (h : c ≤ max a b) : Icc a b ∪ Ici c = Ici (min a c) := by
  grind

@[deprecated Icc_union_Ici (since := "2026-02-22")]
/-
**Set.Icc_union_Ici'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_union_Ici' (h₁ : c <= b) : Icc a b union Ici c = Ici (min a c)
参数：h₁ : c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Icc_union_Ici`：Icc_union_Ici (h : c <= max a b) : Icc a b union Ici 
c = Ici (min a c)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem Icc_union_Ici' (h₁ : c ≤ b) : Icc a b ∪ Ici c = Ici (min a c) :=
  Icc_union_Ici (h₁.trans (le_max_right ..))

/-! ### An infinite and a finite interval -/

/-
**Set.Iic_subset_Iio_union_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_subset_Iio_union_Icc : Iic b subseteq Iio a union Icc a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a

--- 原说明 ---
### An infinite and a finite interval
-/
theorem Iic_subset_Iio_union_Icc : Iic b ⊆ Iio a ∪ Icc a b := fun x hx =>
  (lt_or_ge x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩

@[simp]
/-
**Set.Iio_union_Icc_eq_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_union_Icc_eq_Iic (h : a <= b) : Iio a union Icc a b = Iic b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Iic_subset_Iio_union_Icc`：Iic_subset_Iio_union_Icc : Iic b subseteq 
Iio a union Icc a b
-/
theorem Iio_union_Icc_eq_Iic (h : a ≤ b) : Iio a ∪ Icc a b = Iic b :=
  Subset.antisymm (fun _ hx => hx.elim (fun hx => (le_of_lt hx).trans h) And.right)
    Iic_subset_Iio_union_Icc
/-
**Set.Iio_subset_Iio_union_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_subset_Iio_union_Ico : Iio b subseteq Iio a union Ico a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
-/
theorem Iio_subset_Iio_union_Ico : Iio b ⊆ Iio a ∪ Ico a b := fun x hx =>
  (lt_or_ge x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩

@[simp]
/-
**Set.Iio_union_Ico_eq_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_union_Ico_eq_Iio (h : a <= b) : Iio a union Ico a b = Iio b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Iio_subset_Iio_union_Ico`：Iio_subset_Iio_union_Ico : Iio b subseteq 
Iio a union Ico a b
-/
theorem Iio_union_Ico_eq_Iio (h : a ≤ b) : Iio a ∪ Ico a b = Iio b :=
  Subset.antisymm (fun _ hx => hx.elim (fun hx' => lt_of_lt_of_le hx' h) And.right)
    Iio_subset_Iio_union_Ico
/-
**Set.Iio_union_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_union_Ico (h : min c d <= b) : Iio b union Ico c d = Iio (max b d)
参数：h : min c d <= b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iio_union_Ico (h : min c d ≤ b) : Iio b ∪ Ico c d = Iio (max b d) := by
  grind

@[deprecated Iio_union_Ico (since := "2026-02-22")]
/-
**Set.Iio_union_Ico'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_union_Ico' (h₁ : c <= b) : Iio b union Ico c d = Iio (max b d)
参数：h₁ : c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Iio_union_Ico`：Iio_union_Ico (h : min c d <= b) : Iio b union Ico c 
d = Iio (max b d)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
-/
theorem Iio_union_Ico' (h₁ : c ≤ b) : Iio b ∪ Ico c d = Iio (max b d) :=
  Iio_union_Ico ((min_le_left ..).trans h₁)
/-
**Set.Iic_subset_Iic_union_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_subset_Iic_union_Ioc : Iic b subseteq Iic a union Ioc a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
-/
theorem Iic_subset_Iic_union_Ioc : Iic b ⊆ Iic a ∪ Ioc a b := fun x hx =>
  (le_or_gt x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩

@[simp]
/-
**Set.Iic_union_Ioc_eq_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_union_Ioc_eq_Iic (h : a <= b) : Iic a union Ioc a b = Iic b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Iic_subset_Iic_union_Ioc`：Iic_subset_Iic_union_Ioc : Iic b subseteq 
Iic a union Ioc a b
-/
theorem Iic_union_Ioc_eq_Iic (h : a ≤ b) : Iic a ∪ Ioc a b = Iic b :=
  Subset.antisymm (fun _ hx => hx.elim (fun hx' => le_trans hx' h) And.right)
    Iic_subset_Iic_union_Ioc
/-
**Set.Iic_union_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_union_Ioc (h : min c d < b) : Iic b union Ioc c d = Iic (max b d)
参数：h : min c d < b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iic_union_Ioc (h : min c d < b) : Iic b ∪ Ioc c d = Iic (max b d) := by
  grind

@[deprecated Iic_union_Ioc (since := "2026-02-22")]
/-
**Set.Iic_union_Ioc'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_union_Ioc' (h₁ : c < b) : Iic b union Ioc c d = Iic (max b d)
参数：h₁ : c < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Iic_union_Ioc`：Iic_union_Ioc (h : min c d < b) : Iic b union Ioc c d
 = Iic (max b d)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
-/
theorem Iic_union_Ioc' (h₁ : c < b) : Iic b ∪ Ioc c d = Iic (max b d) :=
  Iic_union_Ioc ((min_le_left ..).trans_lt h₁)
/-
**Set.Iio_subset_Iic_union_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_subset_Iic_union_Ioo : Iio b subseteq Iic a union Ioo a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
-/
theorem Iio_subset_Iic_union_Ioo : Iio b ⊆ Iic a ∪ Ioo a b := fun x hx =>
  (le_or_gt x a).elim (fun hxa => Or.inl hxa) fun hxa => Or.inr ⟨hxa, hx⟩

@[simp]
/-
**Set.Iic_union_Ioo_eq_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_union_Ioo_eq_Iio (h : a < b) : Iic a union Ioo a b = Iio b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Iio_subset_Iic_union_Ioo`：Iio_subset_Iic_union_Ioo : Iio b subseteq 
Iic a union Ioo a b
-/
theorem Iic_union_Ioo_eq_Iio (h : a < b) : Iic a ∪ Ioo a b = Iio b :=
  Subset.antisymm (fun _ hx => hx.elim (fun hx' => lt_of_le_of_lt hx' h) And.right)
    Iio_subset_Iic_union_Ioo
/-
**Set.Iio_union_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_union_Ioo (h : min c d < b) : Iio b union Ioo c d = Iio (max b d)
参数：h : min c d < b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iio_union_Ioo (h : min c d < b) : Iio b ∪ Ioo c d = Iio (max b d) := by
  grind

@[deprecated Iio_union_Ioo (since := "2026-02-22")]
/-
**Set.Iio_union_Ioo'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_union_Ioo' (h₁ : c < b) : Iio b union Ioo c d = Iio (max b d)
参数：h₁ : c < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Iio_union_Ioo`：Iio_union_Ioo (h : min c d < b) : Iio b union Ioo c d
 = Iio (max b d)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
-/
theorem Iio_union_Ioo' (h₁ : c < b) : Iio b ∪ Ioo c d = Iio (max b d) :=
  Iio_union_Ioo ((min_le_left ..).trans_lt h₁)
/-
**Set.Iic_subset_Iic_union_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_subset_Iic_union_Icc : Iic b subseteq Iic a union Icc a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.Iic_subset_Iic_union_Ioc`：Iic_subset_Iic_union_Ioc : Iic b subseteq 
Iic a union Ioc a b
· 使用定理 `Set.union_subset_union_right`：union_subset_union_right (s) {t₁ t₂ : Set 
α} (h : t₁ subseteq t₂) : s union t₁ subseteq s union t₂
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
-/
theorem Iic_subset_Iic_union_Icc : Iic b ⊆ Iic a ∪ Icc a b :=
  Subset.trans Iic_subset_Iic_union_Ioc (union_subset_union_right _ Ioc_subset_Icc_self)

@[simp]
/-
**Set.Iic_union_Icc_eq_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_union_Icc_eq_Iic (h : a <= b) : Iic a union Icc a b = Iic b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Iic_subset_Iic_union_Icc`：Iic_subset_Iic_union_Icc : Iic b subseteq 
Iic a union Icc a b
-/
theorem Iic_union_Icc_eq_Iic (h : a ≤ b) : Iic a ∪ Icc a b = Iic b :=
  Subset.antisymm (fun _ hx => hx.elim (fun hx' => le_trans hx' h) And.right)
    Iic_subset_Iic_union_Icc
/-
**Set.Iic_union_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_union_Icc (h : min c d <= b) : Iic b union Icc c d = Iic (max b d)
参数：h : min c d <= b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iic_union_Icc (h : min c d ≤ b) : Iic b ∪ Icc c d = Iic (max b d) := by
  grind

@[deprecated Iic_union_Icc (since := "2026-02-22")]
/-
**Set.Iic_union_Icc'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_union_Icc' (h₁ : c <= b) : Iic b union Icc c d = Iic (max b d)
参数：h₁ : c <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Iic_union_Icc`：Iic_union_Icc (h : min c d <= b) : Iic b union Icc c 
d = Iic (max b d)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
-/
theorem Iic_union_Icc' (h₁ : c ≤ b) : Iic b ∪ Icc c d = Iic (max b d) :=
  Iic_union_Icc ((min_le_left ..).trans h₁)
/-
**Set.Iio_subset_Iic_union_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_subset_Iic_union_Ico : Iio b subseteq Iic a union Ico a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.Iio_subset_Iic_union_Ioo`：Iio_subset_Iic_union_Ioo : Iio b subseteq 
Iic a union Ioo a b
· 使用定理 `Set.union_subset_union_right`：union_subset_union_right (s) {t₁ t₂ : Set 
α} (h : t₁ subseteq t₂) : s union t₁ subseteq s union t₂
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b
-/
theorem Iio_subset_Iic_union_Ico : Iio b ⊆ Iic a ∪ Ico a b :=
  Subset.trans Iio_subset_Iic_union_Ioo (union_subset_union_right _ Ioo_subset_Ico_self)

@[simp]
/-
**Set.Iic_union_Ico_eq_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_union_Ico_eq_Iio (h : a < b) : Iic a union Ico a b = Iio b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Iio_subset_Iic_union_Ico`：Iio_subset_Iic_union_Ico : Iio b subseteq 
Iic a union Ico a b
-/
theorem Iic_union_Ico_eq_Iio (h : a < b) : Iic a ∪ Ico a b = Iio b :=
  Subset.antisymm (fun _ hx => hx.elim (fun hx' => lt_of_le_of_lt hx' h) And.right)
    Iio_subset_Iic_union_Ico

/-! ### Two finite intervals, `I?o` and `Ic?` -/

/-
**Set.Ioo_subset_Ioo_union_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_subset_Ioo_union_Ico : Ioo a c subseteq Ioo a b union Ico b c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
### Two finite intervals, `I?o` and `Ic?`
-/
theorem Ioo_subset_Ioo_union_Ico : Ioo a c ⊆ Ioo a b ∪ Ico b c := fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
/-
**Set.Ioo_union_Ico_eq_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_union_Ico_eq_Ioo (h₁ : a < b) (h₂ : b <= c) : Ioo a b union Ico b c = 
Ioo a c
参数：h₁ : a < b；h₂ : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Ioo_subset_Ioo_union_Ico`：Ioo_subset_Ioo_union_Ico : Ioo a c subsete
q Ioo a b union Ico b c
-/
theorem Ioo_union_Ico_eq_Ioo (h₁ : a < b) (h₂ : b ≤ c) : Ioo a b ∪ Ico b c = Ioo a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_le h₂⟩) fun hx => ⟨h₁.trans_le hx.1, hx.2⟩)
    Ioo_subset_Ioo_union_Ico
/-
**Set.Ico_subset_Ico_union_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_subset_Ico_union_Ico : Ico a c subseteq Ico a b union Ico b c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Ico_subset_Ico_union_Ico : Ico a c ⊆ Ico a b ∪ Ico b c := fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
/-
**Set.Ico_union_Ico_eq_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_union_Ico_eq_Ico (h₁ : a <= b) (h₂ : b <= c) : Ico a b union Ico b c =
 Ico a c
参数：h₁ : a <= b；h₂ : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ico_subset_Ico_union_Ico`：Ico_subset_Ico_union_Ico : Ico a c subsete
q Ico a b union Ico b c
-/
theorem Ico_union_Ico_eq_Ico (h₁ : a ≤ b) (h₂ : b ≤ c) : Ico a b ∪ Ico b c = Ico a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_le h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Ico_subset_Ico_union_Ico
/-
**Set.Ico_union_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_union_Ico (h₁ : min a b <= max c d) (h₂ : min c d <= max a b) : Ico a 
b union Ico c d = Ico (min a c) (max b d)
参数：h₁ : min a b <= max c d；h₂ : min c d <= max a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ico_union_Ico (h₁ : min a b ≤ max c d) (h₂ : min c d ≤ max a b) :
    Ico a b ∪ Ico c d = Ico (min a c) (max b d) := by
  grind

/-- This is a special case of `Ico_union_Ico` -/
/-
**Set.Ico_union_Ico'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_union_Ico' (h₁ : c <= b) (h₂ : a <= d) : Ico a b union Ico c d = Ico (
min a c) (max b d)
参数：h₁ : c <= b；h₂ : a <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ico_union_Ico`：Ico_union_Ico (h₁ : min a b <= max c d) (h₂ : min c d
 <= max a b) : Ico a b union Ico c d = Ico (min a c) (max b d)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b

--- 原说明 ---
This is a special case of `Ico_union_Ico`
-/
theorem Ico_union_Ico' (h₁ : c ≤ b) (h₂ : a ≤ d) : Ico a b ∪ Ico c d = Ico (min a c) (max b d) :=
  Ico_union_Ico
    ((min_le_left ..).trans (h₂.trans (le_max_right ..)))
    ((min_le_left ..).trans (h₁.trans (le_max_right ..)))
/-
**Set.Icc_subset_Ico_union_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_subset_Ico_union_Icc : Icc a c subseteq Ico a b union Icc b c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Icc_subset_Ico_union_Icc : Icc a c ⊆ Ico a b ∪ Icc b c := fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
/-
**Set.Ico_union_Icc_eq_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_union_Icc_eq_Icc (h₁ : a <= b) (h₂ : b <= c) : Ico a b union Icc b c =
 Icc a c
参数：h₁ : a <= b；h₂ : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Icc_subset_Ico_union_Icc`：Icc_subset_Ico_union_Icc : Icc a c subsete
q Ico a b union Icc b c
-/
theorem Ico_union_Icc_eq_Icc (h₁ : a ≤ b) (h₂ : b ≤ c) : Ico a b ∪ Icc b c = Icc a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.le.trans h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Icc_subset_Ico_union_Icc
/-
**Set.Ioc_subset_Ioo_union_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_subset_Ioo_union_Icc : Ioc a c subseteq Ioo a b union Icc b c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Ioc_subset_Ioo_union_Icc : Ioc a c ⊆ Ioo a b ∪ Icc b c := fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
/-
**Set.Ioo_union_Icc_eq_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_union_Icc_eq_Ioc (h₁ : a < b) (h₂ : b <= c) : Ioo a b union Icc b c = 
Ioc a c
参数：h₁ : a < b；h₂ : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Set.Ioc_subset_Ioo_union_Icc`：Ioc_subset_Ioo_union_Icc : Ioc a c subsete
q Ioo a b union Icc b c
-/
theorem Ioo_union_Icc_eq_Ioc (h₁ : a < b) (h₂ : b ≤ c) : Ioo a b ∪ Icc b c = Ioc a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.le.trans h₂⟩) fun hx => ⟨h₁.trans_le hx.1, hx.2⟩)
    Ioc_subset_Ioo_union_Icc

/-! ### Two finite intervals, `I?c` and `Io?` -/

@[to_dual none]
/-
**Set.Ioo_subset_Ioc_union_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_subset_Ioc_union_Ioo : Ioo a c subseteq Ioc a b union Ioo b c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
### Two finite intervals, `I?c` and `Io?`
-/
theorem Ioo_subset_Ioc_union_Ioo : Ioo a c ⊆ Ioc a b ∪ Ioo b c := fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
/-
**Set.Ioc_union_Ioo_eq_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_union_Ioo_eq_Ioo (h₁ : a <= b) (h₂ : b < c) : Ioc a b union Ioo b c = 
Ioo a c
参数：h₁ : a <= b；h₂ : b < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Ioo_subset_Ioc_union_Ioo`：Ioo_subset_Ioc_union_Ioo : Ioo a c subsete
q Ioc a b union Ioo b c
-/
theorem Ioc_union_Ioo_eq_Ioo (h₁ : a ≤ b) (h₂ : b < c) : Ioc a b ∪ Ioo b c = Ioo a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_lt h₂⟩) fun hx => ⟨h₁.trans_lt hx.1, hx.2⟩)
    Ioo_subset_Ioc_union_Ioo

@[to_dual none]
/-
**Set.Ico_subset_Icc_union_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_subset_Icc_union_Ioo : Ico a c subseteq Icc a b union Ioo b c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Ico_subset_Icc_union_Ioo : Ico a c ⊆ Icc a b ∪ Ioo b c := fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp, to_dual none]
/-
**Set.Icc_union_Ioo_eq_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_union_Ioo_eq_Ico (h₁ : a <= b) (h₂ : b < c) : Icc a b union Ioo b c = 
Ico a c
参数：h₁ : a <= b；h₂ : b < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.Ico_subset_Icc_union_Ioo`：Ico_subset_Icc_union_Ioo : Ico a c subsete
q Icc a b union Ioo b c
-/
theorem Icc_union_Ioo_eq_Ico (h₁ : a ≤ b) (h₂ : b < c) : Icc a b ∪ Ioo b c = Ico a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_lt h₂⟩) fun hx => ⟨h₁.trans hx.1.le, hx.2⟩)
    Ico_subset_Icc_union_Ioo
/-
**Set.Icc_subset_Icc_union_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_subset_Icc_union_Ioc : Icc a c subseteq Icc a b union Ioc b c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Icc_subset_Icc_union_Ioc : Icc a c ⊆ Icc a b ∪ Ioc b c := fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
/-
**Set.Icc_union_Ioc_eq_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_union_Ioc_eq_Icc (h₁ : a <= b) (h₂ : b <= c) : Icc a b union Ioc b c =
 Icc a c
参数：h₁ : a <= b；h₂ : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.Icc_subset_Icc_union_Ioc`：Icc_subset_Icc_union_Ioc : Icc a c subsete
q Icc a b union Ioc b c
-/
theorem Icc_union_Ioc_eq_Icc (h₁ : a ≤ b) (h₂ : b ≤ c) : Icc a b ∪ Ioc b c = Icc a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans hx.1.le, hx.2⟩)
    Icc_subset_Icc_union_Ioc
/-
**Set.Ioc_subset_Ioc_union_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_subset_Ioc_union_Ioc : Ioc a c subseteq Ioc a b union Ioc b c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Ioc_subset_Ioc_union_Ioc : Ioc a c ⊆ Ioc a b ∪ Ioc b c := fun x hx =>
  (le_or_gt x b).elim (fun hxb => Or.inl ⟨hx.1, hxb⟩) fun hxb => Or.inr ⟨hxb, hx.2⟩

@[simp]
/-
**Set.Ioc_union_Ioc_eq_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_union_Ioc_eq_Ioc (h₁ : a <= b) (h₂ : b <= c) : Ioc a b union Ioc b c =
 Ioc a c
参数：h₁ : a <= b；h₂ : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Set.Ioc_subset_Ioc_union_Ioc`：Ioc_subset_Ioc_union_Ioc : Ioc a c subsete
q Ioc a b union Ioc b c
-/
theorem Ioc_union_Ioc_eq_Ioc (h₁ : a ≤ b) (h₂ : b ≤ c) : Ioc a b ∪ Ioc b c = Ioc a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans_lt hx.1, hx.2⟩)
    Ioc_subset_Ioc_union_Ioc
/-
**Set.Ioc_union_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_union_Ioc (h₁ : min a b <= max c d) (h₂ : min c d <= max a b) : Ioc a 
b union Ioc c d = Ioc (min a c) (max b d)
参数：h₁ : min a b <= max c d；h₂ : min c d <= max a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioc_union_Ioc (h₁ : min a b ≤ max c d) (h₂ : min c d ≤ max a b) :
    Ioc a b ∪ Ioc c d = Ioc (min a c) (max b d) := by
  grind

/-- This is a special case of `Ioc_union_Ioc` -/
/-
**Set.Ioc_union_Ioc'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_union_Ioc' (h₁ : c <= b) (h₂ : a <= d) : Ioc a b union Ioc c d = Ioc (
min a c) (max b d)
参数：h₁ : c <= b；h₂ : a <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioc_union_Ioc`：Ioc_union_Ioc (h₁ : min a b <= max c d) (h₂ : min c d
 <= max a b) : Ioc a b union Ioc c d = Ioc (min a c) (max b d)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b

--- 原说明 ---
This is a special case of `Ioc_union_Ioc`
-/
theorem Ioc_union_Ioc' (h₁ : c ≤ b) (h₂ : a ≤ d) : Ioc a b ∪ Ioc c d = Ioc (min a c) (max b d) :=
  Ioc_union_Ioc
    ((min_le_left ..).trans (h₂.trans (le_max_right ..)))
    ((min_le_left ..).trans (h₁.trans (le_max_right ..)))

/-! ### Two finite intervals with a common point -/

@[to_dual none]
/-
**Set.Ioo_subset_Ioc_union_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_subset_Ioc_union_Ico : Ioo a c subseteq Ioc a b union Ico b c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.Ioo_subset_Ioc_union_Ioo`：Ioo_subset_Ioc_union_Ioo : Ioo a c subsete
q Ioc a b union Ioo b c
· 使用定理 `Set.union_subset_union_right`：union_subset_union_right (s) {t₁ t₂ : Set 
α} (h : t₁ subseteq t₂) : s union t₁ subseteq s union t₂
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b

--- 原说明 ---
### Two finite intervals with a common point
-/
theorem Ioo_subset_Ioc_union_Ico : Ioo a c ⊆ Ioc a b ∪ Ico b c :=
  Subset.trans Ioo_subset_Ioc_union_Ioo (union_subset_union_right _ Ioo_subset_Ico_self)

@[to_dual (attr := simp)]
/-
**Set.Ioc_union_Ico_eq_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_union_Ico_eq_Ioo (h₁ : a < b) (h₂ : b < c) : Ioc a b union Ico b c = I
oo a c
参数：h₁ : a < b；h₂ : b < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Set.Ioo_subset_Ioc_union_Ico`：Ioo_subset_Ioc_union_Ico : Ioo a c subsete
q Ioc a b union Ico b c
-/
theorem Ioc_union_Ico_eq_Ioo (h₁ : a < b) (h₂ : b < c) : Ioc a b ∪ Ico b c = Ioo a c :=
  Subset.antisymm
    (fun _ hx =>
      hx.elim (fun hx' => ⟨hx'.1, hx'.2.trans_lt h₂⟩) fun hx' => ⟨h₁.trans_le hx'.1, hx'.2⟩)
    Ioo_subset_Ioc_union_Ico
/-
**Set.Ico_subset_Icc_union_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_subset_Icc_union_Ico : Ico a c subseteq Icc a b union Ico b c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.Ico_subset_Icc_union_Ioo`：Ico_subset_Icc_union_Ioo : Ico a c subsete
q Icc a b union Ioo b c
· 使用定理 `Set.union_subset_union_right`：union_subset_union_right (s) {t₁ t₂ : Set 
α} (h : t₁ subseteq t₂) : s union t₁ subseteq s union t₂
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b
-/
theorem Ico_subset_Icc_union_Ico : Ico a c ⊆ Icc a b ∪ Ico b c :=
  Subset.trans Ico_subset_Icc_union_Ioo (union_subset_union_right _ Ioo_subset_Ico_self)

@[simp]
/-
**Set.Icc_union_Ico_eq_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_union_Ico_eq_Ico (h₁ : a <= b) (h₂ : b < c) : Icc a b union Ico b c = 
Ico a c
参数：h₁ : a <= b；h₂ : b < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ico_subset_Icc_union_Ico`：Ico_subset_Icc_union_Ico : Ico a c subsete
q Icc a b union Ico b c
-/
theorem Icc_union_Ico_eq_Ico (h₁ : a ≤ b) (h₂ : b < c) : Icc a b ∪ Ico b c = Ico a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans_lt h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Ico_subset_Icc_union_Ico
/-
**Set.Icc_subset_Icc_union_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_subset_Icc_union_Icc : Icc a c subseteq Icc a b union Icc b c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.Icc_subset_Icc_union_Ioc`：Icc_subset_Icc_union_Ioc : Icc a c subsete
q Icc a b union Ioc b c
· 使用定理 `Set.union_subset_union_right`：union_subset_union_right (s) {t₁ t₂ : Set 
α} (h : t₁ subseteq t₂) : s union t₁ subseteq s union t₂
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
-/
theorem Icc_subset_Icc_union_Icc : Icc a c ⊆ Icc a b ∪ Icc b c :=
  Subset.trans Icc_subset_Icc_union_Ioc (union_subset_union_right _ Ioc_subset_Icc_self)

@[simp]
/-
**Set.Icc_union_Icc_eq_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_union_Icc_eq_Icc (h₁ : a <= b) (h₂ : b <= c) : Icc a b union Icc b c =
 Icc a c
参数：h₁ : a <= b；h₂ : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Icc_subset_Icc_union_Icc`：Icc_subset_Icc_union_Icc : Icc a c subsete
q Icc a b union Icc b c
-/
theorem Icc_union_Icc_eq_Icc (h₁ : a ≤ b) (h₂ : b ≤ c) : Icc a b ∪ Icc b c = Icc a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans hx.1, hx.2⟩)
    Icc_subset_Icc_union_Icc
/-
**Set.Icc_union_Icc'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_union_Icc' (h₁ : c <= b) (h₂ : a <= d) : Icc a b union Icc c d = Icc (
min a c) (max b d)
参数：h₁ : c <= b；h₂ : a <= d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Icc_union_Icc' (h₁ : c ≤ b) (h₂ : a ≤ d) : Icc a b ∪ Icc c d = Icc (min a c) (max b d) := by
  grind

/-- We cannot replace `<` by `≤` in the hypotheses.
Otherwise for `b < a = d < c` the l.h.s. is `∅` and the r.h.s. is `{a}`.
-/
/-
**Set.Icc_union_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_union_Icc (h₁ : min a b < max c d) (h₂ : min c d < max a b) : Icc a b 
union Icc c d = Icc (min a c) (max b d)
参数：h₁ : min a b < max c d；h₂ : min c d < max a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We cannot replace `<` by `≤` in the hypotheses.
Otherwise for `b < a = d < c` the l.h.s. is `∅` and the r.h.s. is `{a}`.
-/
theorem Icc_union_Icc (h₁ : min a b < max c d) (h₂ : min c d < max a b) :
    Icc a b ∪ Icc c d = Icc (min a c) (max b d) := by
  grind
/-
**Set.Ioc_subset_Ioc_union_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_subset_Ioc_union_Icc : Ioc a c subseteq Ioc a b union Icc b c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.Ioc_subset_Ioc_union_Ioc`：Ioc_subset_Ioc_union_Ioc : Ioc a c subsete
q Ioc a b union Ioc b c
· 使用定理 `Set.union_subset_union_right`：union_subset_union_right (s) {t₁ t₂ : Set 
α} (h : t₁ subseteq t₂) : s union t₁ subseteq s union t₂
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
-/
theorem Ioc_subset_Ioc_union_Icc : Ioc a c ⊆ Ioc a b ∪ Icc b c :=
  Subset.trans Ioc_subset_Ioc_union_Ioc (union_subset_union_right _ Ioc_subset_Icc_self)

@[simp]
/-
**Set.Ioc_union_Icc_eq_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_union_Icc_eq_Ioc (h₁ : a < b) (h₂ : b <= c) : Ioc a b union Icc b c = 
Ioc a c
参数：h₁ : a < b；h₂ : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Set.Ioc_subset_Ioc_union_Icc`：Ioc_subset_Ioc_union_Icc : Ioc a c subsete
q Ioc a b union Icc b c
-/
theorem Ioc_union_Icc_eq_Ioc (h₁ : a < b) (h₂ : b ≤ c) : Ioc a b ∪ Icc b c = Ioc a c :=
  Subset.antisymm
    (fun _ hx => hx.elim (fun hx => ⟨hx.1, hx.2.trans h₂⟩) fun hx => ⟨h₁.trans_le hx.1, hx.2⟩)
    Ioc_subset_Ioc_union_Icc
/-
**Set.Ioo_union_Ioo'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_union_Ioo' (h₁ : c < b) (h₂ : a < d) : Ioo a b union Ioo c d = Ioo (mi
n a c) (max b d)
参数：h₁ : c < b；h₂ : a < d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioo_union_Ioo' (h₁ : c < b) (h₂ : a < d) : Ioo a b ∪ Ioo c d = Ioo (min a c) (max b d) := by
  grind
/-
**Set.Ioo_union_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_union_Ioo (h₁ : min a b < max c d) (h₂ : min c d < max a b) : Ioo a b 
union Ioo c d = Ioo (min a c) (max b d)
参数：h₁ : min a b < max c d；h₂ : min c d < max a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioo_union_Ioo (h₁ : min a b < max c d) (h₂ : min c d < max a b) :
    Ioo a b ∪ Ioo c d = Ioo (min a c) (max b d) := by
  grind
/-
**Set.Ioo_subset_Ioo_union_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_subset_Ioo_union_Ioo (h₁ : a <= a₁) (h₂ : c < b) (h₃ : b₁ <= d) : Ioo 
a₁ b₁ subseteq Ioo a b union Ioo c d
参数：h₁ : a <= a₁；h₂ : c < b；h₃ : b₁ <= d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Ioo_subset_Ioo_union_Ioo (h₁ : a ≤ a₁) (h₂ : c < b) (h₃ : b₁ ≤ d) :
    Ioo a₁ b₁ ⊆ Ioo a b ∪ Ioo c d := fun x hx =>
  (lt_or_ge x b).elim (fun hxb => Or.inl ⟨lt_of_le_of_lt h₁ hx.1, hxb⟩)
    fun hxb => Or.inr ⟨lt_of_lt_of_le h₂ hxb, lt_of_lt_of_le hx.2 h₃⟩

/-! ### Intersection, difference, complement -/

@[to_dual (attr := simp)]
/-
**Set.Ioi_inter_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioi_inter_Ioi : Ioi a inter Ioi b = Ioi (a ⊔ b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `sup_lt_iff`：sup_lt_iff : b ⊔ c < a ↔ b < a ∧ c < a

--- 原说明 ---
### Intersection, difference, complement
-/
theorem Ioi_inter_Ioi : Ioi a ∩ Ioi b = Ioi (a ⊔ b) :=
  ext fun _ => sup_lt_iff.symm

@[to_dual]
/-
**Set.Ico_inter_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_inter_Ico : Ico a₁ b₁ inter Ico a₂ b₂ = Ico (a₁ ⊔ a₂) (b₁ ⊓ b₂)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ico_inter_Ico : Ico a₁ b₁ ∩ Ico a₂ b₂ = Ico (a₁ ⊔ a₂) (b₁ ⊓ b₂) := by
  grind

@[to_dual self]
/-
**Set.Ioo_inter_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_inter_Ioo : Ioo a₁ b₁ inter Ioo a₂ b₂ = Ioo (a₁ ⊔ a₂) (b₁ ⊓ b₂)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioo_inter_Ioo : Ioo a₁ b₁ ∩ Ioo a₂ b₂ = Ioo (a₁ ⊔ a₂) (b₁ ⊓ b₂) := by
  grind

@[to_dual]
/-
**Set.Ioo_inter_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_inter_Iio : Ioo a b inter Iio c = Ioo a (min b c)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioo_inter_Iio : Ioo a b ∩ Iio c = Ioo a (min b c) := by
  grind

@[to_dual]
/-
**Set.Iio_inter_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_inter_Ioo : Iio a inter Ioo b c = Ioo b (min a c)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iio_inter_Ioo : Iio a ∩ Ioo b c = Ioo b (min a c) := by
  grind
/-
**Set.Ioc_inter_Ioo_of_left_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_inter_Ioo_of_left_lt (h : b₁ < b₂) : Ioc a₁ b₁ inter Ioo a₂ b₂ = Ioc (
max a₁ a₂) b₁
参数：h : b₁ < b₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioc_inter_Ioo_of_left_lt (h : b₁ < b₂) : Ioc a₁ b₁ ∩ Ioo a₂ b₂ = Ioc (max a₁ a₂) b₁ := by
  grind
/-
**Set.Ioc_inter_Ioo_of_right_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_inter_Ioo_of_right_le (h : b₂ <= b₁) : Ioc a₁ b₁ inter Ioo a₂ b₂ = Ioo
 (max a₁ a₂) b₂
参数：h : b₂ <= b₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioc_inter_Ioo_of_right_le (h : b₂ ≤ b₁) : Ioc a₁ b₁ ∩ Ioo a₂ b₂ = Ioo (max a₁ a₂) b₂ := by
  grind
/-
**Set.Ioo_inter_Ioc_of_left_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_inter_Ioc_of_left_le (h : b₁ <= b₂) : Ioo a₁ b₁ inter Ioc a₂ b₂ = Ioo 
(max a₁ a₂) b₁
参数：h : b₁ <= b₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioo_inter_Ioc_of_left_le (h : b₁ ≤ b₂) : Ioo a₁ b₁ ∩ Ioc a₂ b₂ = Ioo (max a₁ a₂) b₁ := by
  grind
/-
**Set.Ioo_inter_Ioc_of_right_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_inter_Ioc_of_right_lt (h : b₂ < b₁) : Ioo a₁ b₁ inter Ioc a₂ b₂ = Ioc 
(max a₁ a₂) b₂
参数：h : b₂ < b₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioo_inter_Ioc_of_right_lt (h : b₂ < b₁) : Ioo a₁ b₁ ∩ Ioc a₂ b₂ = Ioc (max a₁ a₂) b₂ := by
  grind

@[simp]
/-
**Set.Ico_sdiff_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_sdiff_Iio : Ico a b \ Iio c = Ico (max a c) b
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ico_sdiff_Iio : Ico a b \ Iio c = Ico (max a c) b := by
  grind

@[deprecated (since := "2026-06-03")] alias Ico_diff_Iio := Ico_sdiff_Iio

@[simp]
/-
**Set.Ioc_sdiff_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_sdiff_Ioi : Ioc a b \ Ioi c = Ioc a (min b c)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioc_sdiff_Ioi : Ioc a b \ Ioi c = Ioc a (min b c) := by
  grind

@[deprecated (since := "2026-06-03")] alias Ioc_diff_Ioi := Ioc_sdiff_Ioi

@[simp]
/-
**Set.Ioc_inter_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_inter_Ioi : Ioc a b inter Ioi c = Ioc (a ⊔ c) b
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioc_inter_Ioi : Ioc a b ∩ Ioi c = Ioc (a ⊔ c) b := by
  grind

@[simp]
/-
**Set.Ico_inter_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_inter_Iio : Ico a b inter Iio c = Ico a (min b c)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ico_inter_Iio : Ico a b ∩ Iio c = Ico a (min b c) := by
  grind

@[simp]
/-
**Set.Ioc_sdiff_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_sdiff_Iic : Ioc a b \ Iic c = Ioc (max a c) b
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioc_sdiff_Iic : Ioc a b \ Iic c = Ioc (max a c) b := by
  grind

@[deprecated (since := "2026-06-03")] alias Ioc_diff_Iic := Ioc_sdiff_Iic
/-
**Set.compl_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_Ioc : (Ioc a b)ᶜ = Iic a union Ioi b
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compl_Ioc : (Ioc a b)ᶜ = Iic a ∪ Ioi b := by
  grind
/-
**Set.Iic_sdiff_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_sdiff_Ioc : Iic b \ Ioc a b = Iic (a ⊓ b)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iic_sdiff_Ioc : Iic b \ Ioc a b = Iic (a ⊓ b) := by
  grind

@[deprecated (since := "2026-06-03")] alias Iic_diff_Ioc := Iic_sdiff_Ioc

@[simp]
/-
**Set.Ioi_sdiff_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioi_sdiff_Ioc : Ioi a \ Ioc a b = Ioi (max a b)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioi_sdiff_Ioc : Ioi a \ Ioc a b = Ioi (max a b) := by
  grind

@[deprecated (since := "2026-06-03")] alias Ioi_diff_Ioc := Ioi_sdiff_Ioc
/-
**Set.Iic_sdiff_Ioc_self_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_sdiff_Ioc_self_of_le (hab : a <= b) : Iic b \ Ioc a b = Iic a
参数：hab : a <= b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iic_sdiff_Ioc_self_of_le (hab : a ≤ b) : Iic b \ Ioc a b = Iic a := by
  grind

@[deprecated (since := "2026-06-03")] alias Iic_diff_Ioc_self_of_le := Iic_sdiff_Ioc_self_of_le

@[simp]
/-
**Set.Ioc_union_Ioc_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_union_Ioc_right : Ioc a b union Ioc a c = Ioc a (max b c)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioc_union_Ioc_right : Ioc a b ∪ Ioc a c = Ioc a (max b c) := by
  grind

@[simp]
/-
**Set.Ioc_union_Ioc_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_union_Ioc_left : Ioc a c union Ioc b c = Ioc (min a b) c
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioc_union_Ioc_left : Ioc a c ∪ Ioc b c = Ioc (min a b) c := by
  grind

@[simp]
/-
**Set.Ioc_union_Ioc_symm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_union_Ioc_symm : Ioc a b union Ioc b a = Ioc (min a b) (max a b)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioc_union_Ioc_symm : Ioc a b ∪ Ioc b a = Ioc (min a b) (max a b) := by
  grind

@[simp]
/-
**Set.Ioc_union_Ioc_union_Ioc_cycle** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_union_Ioc_union_Ioc_cycle : Ioc a b union Ioc b c union Ioc c a = Ioc 
(min a (min b c)) (max a (max b c))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ioc_union_Ioc_union_Ioc_cycle :
    Ioc a b ∪ Ioc b c ∪ Ioc c a = Ioc (min a (min b c)) (max a (max b c)) := by
  grind

end Set

