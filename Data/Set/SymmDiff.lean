/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.SymmDiff

/-! # Symmetric differences of sets -/

public section

assert_not_exists RelIso

namespace Set

universe u
variable {α : Type u} {a : α} {s t u v : Set α}

open scoped symmDiff

/-
**Set.mem_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {a : α} {s t : Set α}, a ∈ symmDiff s t ↔ a ∈ s ∧ a ∉ t ∨ a
 ∈ t ∧ a ∉ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[grind =] theorem mem_symmDiff : a ∈ s ∆ t ↔ a ∈ s ∧ a ∉ t ∨ a ∈ t ∧ a ∉ s := .rfl
/-
**Set.symmDiff_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} (s t : Set α), symmDiff s t = s \ t ∪ t \ s
参数：s t : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem symmDiff_def (s t : Set α) : s ∆ t = s \ t ∪ t \ s := rfl
/-
**Set.mem_bihimp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {a : α} {s t : Set α}, a ∈ bihimp s t ↔ (a ∈ s ↔ a ∈ t)
参数：a ∈ s ↔ a ∈ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem mem_bihimp_iff : a ∈ s ⇔ t ↔ (a ∈ s ↔ a ∈ t) := by simp [bihimp, iff_def']
/-
**Set.bihimp_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {s t : Set α}, bihimp s t = (s ∪ tᶜ) ∩ (t ∪ sᶜ)
参数：s ∪ tᶜ；t ∪ sᶜ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bihimp_eq`：bihimp_eq : a ⇔ b = (a ⊔ bᶜ) ⊓ (b ⊔ aᶜ)
-/
protected theorem bihimp_def : s ⇔ t = (s ∪ tᶜ) ∩ (t ∪ sᶜ) := bihimp_eq ..
/-
**Set.symmDiff_subset_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：symmDiff_subset_union : s ∆ t subseteq s union t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_le_sup`：symmDiff_le_sup {a b : α} : a ∆ b <= a ⊔ b
-/
theorem symmDiff_subset_union : s ∆ t ⊆ s ∪ t :=
  @symmDiff_le_sup (Set α) _ _ _

@[simp]
/-
**Set.symmDiff_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：symmDiff_eq_empty : s ∆ t = ∅ ↔ s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symmDiff_eq_bot`：symmDiff_eq_bot {a b : α} : a ∆ b = ⊥ ↔ a = b
-/
theorem symmDiff_eq_empty : s ∆ t = ∅ ↔ s = t :=
  symmDiff_eq_bot

@[simp]
/-
**Set.symmDiff_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：symmDiff_nonempty : (s ∆ t).Nonempty ↔ s != t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Set.symmDiff_eq_empty`：symmDiff_eq_empty : s ∆ t = ∅ ↔ s = t
-/
theorem symmDiff_nonempty : (s ∆ t).Nonempty ↔ s ≠ t :=
  nonempty_iff_ne_empty.trans symmDiff_eq_empty.not
/-
**Set.inter_symmDiff_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_symmDiff_distrib_left (s t u : Set α) : s inter t ∆ u = (s inter t) 
∆ (s inter u)
参数：s t u : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_symmDiff_distrib_left`：inf_symmDiff_distrib_left : a ⊓ b ∆ c = (a ⊓ 
b) ∆ (a ⊓ c)
-/
theorem inter_symmDiff_distrib_left (s t u : Set α) : s ∩ t ∆ u = (s ∩ t) ∆ (s ∩ u) :=
  inf_symmDiff_distrib_left _ _ _
/-
**Set.inter_symmDiff_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_symmDiff_distrib_right (s t u : Set α) : s ∆ t inter u = (s inter u)
 ∆ (t inter u)
参数：s t u : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_symmDiff_distrib_right`：inf_symmDiff_distrib_right : a ∆ b ⊓ c = (a 
⊓ c) ∆ (b ⊓ c)
-/
theorem inter_symmDiff_distrib_right (s t u : Set α) : s ∆ t ∩ u = (s ∩ u) ∆ (t ∩ u) :=
  inf_symmDiff_distrib_right _ _ _
/-
**Set.subset_symmDiff_union_symmDiff_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_symmDiff_union_symmDiff_left (h : Disjoint s t) : u subseteq s ∆ u 
union t ∆ u
参数：h : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.le_symmDiff_sup_symmDiff_left`：Disjoint.le_symmDiff_sup_symmDif
f_left (h : Disjoint a b) : c <= a ∆ c ⊔ b ∆ c
-/
theorem subset_symmDiff_union_symmDiff_left (h : Disjoint s t) : u ⊆ s ∆ u ∪ t ∆ u :=
  h.le_symmDiff_sup_symmDiff_left
/-
**Set.subset_symmDiff_union_symmDiff_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_symmDiff_union_symmDiff_right (h : Disjoint t u) : s subseteq s ∆ t
 union s ∆ u
参数：h : Disjoint t u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.le_symmDiff_sup_symmDiff_right`：Disjoint.le_symmDiff_sup_symmDi
ff_right (h : Disjoint b c) : a <= a ∆ b ⊔ a ∆ c
-/
theorem subset_symmDiff_union_symmDiff_right (h : Disjoint t u) : s ⊆ s ∆ t ∪ s ∆ u :=
  h.le_symmDiff_sup_symmDiff_right
/-
**Set.union_symmDiff_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：union_symmDiff_subset : (s union t) ∆ u subseteq s ∆ u union t ∆ u
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma union_symmDiff_subset : (s ∪ t) ∆ u ⊆ s ∆ u ∪ t ∆ u := by
  grind
/-
**Set.symmDiff_union_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：symmDiff_union_subset : s ∆ (t union u) subseteq s ∆ t union s ∆ u
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symmDiff_union_subset : s ∆ (t ∪ u) ⊆ s ∆ t ∪ s ∆ u := by
  grind
/-
**Set.union_symmDiff_union_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：union_symmDiff_union_subset : (s union t) ∆ (u union v) subseteq s ∆ u uni
on t ∆ v
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma union_symmDiff_union_subset : (s ∪ t) ∆ (u ∪ v) ⊆ s ∆ u ∪ t ∆ v := by
  grind

end Set

