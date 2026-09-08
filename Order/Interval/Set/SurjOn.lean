/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Data.Set.Function
public import Mathlib.Order.Interval.Set.LinearOrder

/-!
# Monotone surjective functions are surjective on intervals

A monotone surjective function sends any interval in the domain onto the interval with corresponding
endpoints in the range.  This is expressed in this file using `Set.surjOn`, and provided for all
permutations of interval endpoints.
-/

public section


variable {α : Type*} {β : Type*} [LinearOrder α] [PartialOrder β] {f : α → β}

open Set Function

open OrderDual (toDual)

/-
**surjOn_Ioo_of_monotone_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：surjOn_Ioo_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function
.Surjective f) (a b : α) : SurjOn f (Ioo a b) (Ioo (f a) (f b))
参数：h_mono : Monotone f；h_surj : Function.Surjective f；a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oo a b ↔ a < x ∧ x < b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Monotone.reflect_lt`：Monotone.reflect_lt (hf : Monotone f) {a b : α} (h 
: f a < f b) : a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem surjOn_Ioo_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a b : α) : SurjOn f (Ioo a b) (Ioo (f a) (f b)) := by
  intro p hp
  rcases h_surj p with ⟨x, rfl⟩
  refine ⟨x, mem_Ioo.2 ?_, rfl⟩
  contrapose! hp
  exact fun h => h.2.not_ge (h_mono <| hp <| h_mono.reflect_lt h.1)
/-
**surjOn_Ico_of_monotone_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：surjOn_Ico_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function
.Surjective f) (a b : α) : SurjOn f (Ico a b) (Ico (f a) (f b))
参数：h_mono : Monotone f；h_surj : Function.Surjective f；a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Set.eq_left_or_mem_Ioo_of_mem_Ico`：eq_left_or_mem_Ioo_of_mem_Ico {x : α}
 (hmem : x in Ico a b) : x = a ∨ x in Ioo a b
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Ico a b ↔ a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b
· 使用定理 `surjOn_Ioo_of_monotone_surjective`：surjOn_Ioo_of_monotone_surjective (h_
mono : Monotone f) (h_surj : Function.Surjective f) (a b : α) : SurjOn f (Ioo a 
b) (Ioo (f a) (f b))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ico_eq_empty`：Ico_eq_empty (h : ¬a < b) : Ico a b = ∅
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Set.surjOn_empty`：surjOn_empty (f : α -> β) (s : Set α) : SurjOn f s ∅
-/
theorem surjOn_Ico_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a b : α) : SurjOn f (Ico a b) (Ico (f a) (f b)) := by
  obtain hab | hab := lt_or_ge a b
  · intro p hp
    rcases eq_left_or_mem_Ioo_of_mem_Ico hp with (rfl | hp')
    · exact mem_image_of_mem f (left_mem_Ico.mpr hab)
    · exact image_mono Ioo_subset_Ico_self <|
        surjOn_Ioo_of_monotone_surjective h_mono h_surj a b hp'
  · rw [Ico_eq_empty (h_mono hab).not_gt]
    exact surjOn_empty f _
/-
**surjOn_Ioc_of_monotone_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：surjOn_Ioc_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function
.Surjective f) (a b : α) : SurjOn f (Ioc a b) (Ioc (f a) (f b))
参数：h_mono : Monotone f；h_surj : Function.Surjective f；a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ico_toDual`：Ico_toDual : Ico (toDual a) (toDual b) = ofDual ⁻¹' Ioc 
b a
· 使用定理 `surjOn_Ico_of_monotone_surjective`：surjOn_Ico_of_monotone_surjective (h_
mono : Monotone f) (h_surj : Function.Surjective f) (a b : α) : SurjOn f (Ico a 
b) (Ico (f a) (f b))
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
-/
theorem surjOn_Ioc_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a b : α) : SurjOn f (Ioc a b) (Ioc (f a) (f b)) := by
  simpa using! surjOn_Ico_of_monotone_surjective h_mono.dual h_surj (toDual b) (toDual a)

-- to see that the hypothesis `a ≤ b` is necessary, consider a constant function
/-
**surjOn_Icc_of_monotone_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：surjOn_Icc_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function
.Surjective f) {a b : α} (hab : a <= b) : SurjOn f (Icc a b) (Icc (f a) (f b))
参数：h_mono : Monotone f；h_surj : Function.Surjective f；hab : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_endpoints_or_mem_Ioo_of_mem_Icc`：eq_endpoints_or_mem_Ioo_of_mem_I
cc {x : α} (hmem : x in Icc a b) : x = a ∨ x = b ∨ x in Ioo a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `surjOn_Ioo_of_monotone_surjective`：surjOn_Ioo_of_monotone_surjective (h_
mono : Monotone f) (h_surj : Function.Surjective f) (a b : α) : SurjOn f (Ioo a 
b) (Ioo (f a) (f b))
-/
theorem surjOn_Icc_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    {a b : α} (hab : a ≤ b) : SurjOn f (Icc a b) (Icc (f a) (f b)) := by
  intro p hp
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hp with (rfl | rfl | hp')
  · exact ⟨a, left_mem_Icc.mpr hab, rfl⟩
  · exact ⟨b, right_mem_Icc.mpr hab, rfl⟩
  · exact image_mono Ioo_subset_Icc_self <|
      surjOn_Ioo_of_monotone_surjective h_mono h_surj a b hp'
/-
**surjOn_Ioi_of_monotone_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：surjOn_Ioi_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function
.Surjective f) (a : α) : SurjOn f (Ioi a) (Ioi (f a))
参数：h_mono : Monotone f；h_surj : Function.Surjective f；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.compl_Iic`：compl_Iic : (Iic a)ᶜ = Ioi a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.MapsTo.surjOn_compl`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β},   Set.MapsTo f s t → Function.Surjective f → Set.SurjOn f 
sᶜ tᶜ
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
-/
theorem surjOn_Ioi_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a : α) : SurjOn f (Ioi a) (Ioi (f a)) := by
  rw [← compl_Iic, ← compl_compl (Ioi (f a))]
  refine MapsTo.surjOn_compl ?_ h_surj
  exact fun x hx => (h_mono hx).not_gt
/-
**surjOn_Iio_of_monotone_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：surjOn_Iio_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function
.Surjective f) (a : α) : SurjOn f (Iio a) (Iio (f a))
参数：h_mono : Monotone f；h_surj : Function.Surjective f；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `surjOn_Ioi_of_monotone_surjective`：surjOn_Ioi_of_monotone_surjective (h_
mono : Monotone f) (h_surj : Function.Surjective f) (a : α) : SurjOn f (Ioi a) (
Ioi (f a))
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
-/
theorem surjOn_Iio_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a : α) : SurjOn f (Iio a) (Iio (f a)) :=
  @surjOn_Ioi_of_monotone_surjective _ _ _ _ _ h_mono.dual h_surj a
/-
**surjOn_Ici_of_monotone_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：surjOn_Ici_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function
.Surjective f) (a : α) : SurjOn f (Ici a) (Ici (f a))
参数：h_mono : Monotone f；h_surj : Function.Surjective f；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioi_union_left`：∀ {α : Type u_1} [inst : PartialOrder α] {a : α}, Se
t.Ioi a ∪ {a} = Set.Ici a
· 使用定理 `Set.SurjOn.union_union`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} 
{t₁ t₂ : Set β} {f : α → β},   Set.SurjOn f s₁ t₁ → Set.SurjOn f s₂ t₂ → Set.Sur
jOn f (s₁ ∪ …
· 使用定理 `surjOn_Ioi_of_monotone_surjective`：surjOn_Ioi_of_monotone_surjective (h_
mono : Monotone f) (h_surj : Function.Surjective f) (a : α) : SurjOn f (Ioi a) (
Ioi (f a))
· 使用定理 `Set.surjOn_image`：surjOn_image (f : α -> β) (s : Set α) : SurjOn f s (f 
'' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
-/
theorem surjOn_Ici_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a : α) : SurjOn f (Ici a) (Ici (f a)) := by
  rw [← Ioi_union_left, ← Ioi_union_left]
  exact
    (surjOn_Ioi_of_monotone_surjective h_mono h_surj a).union_union
      (@image_singleton _ _ f a ▸ surjOn_image _ _)
/-
**surjOn_Iic_of_monotone_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：surjOn_Iic_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function
.Surjective f) (a : α) : SurjOn f (Iic a) (Iic (f a))
参数：h_mono : Monotone f；h_surj : Function.Surjective f；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `surjOn_Ici_of_monotone_surjective`：surjOn_Ici_of_monotone_surjective (h_
mono : Monotone f) (h_surj : Function.Surjective f) (a : α) : SurjOn f (Ici a) (
Ici (f a))
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
-/
theorem surjOn_Iic_of_monotone_surjective (h_mono : Monotone f) (h_surj : Function.Surjective f)
    (a : α) : SurjOn f (Iic a) (Iic (f a)) :=
  @surjOn_Ici_of_monotone_surjective _ _ _ _ _ h_mono.dual h_surj a
