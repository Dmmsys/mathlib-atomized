/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
module

public import Mathlib.Order.UpperLower.Closure

/-!
# Upper and lower set product

The Cartesian product of sets carries over to upper and lower sets in a natural way. This file
defines said product over the types `UpperSet` and `LowerSet` and proves some of its properties.

## Notation

* `×ˢ` is notation for `UpperSet.prod` / `LowerSet.prod`.
-/

@[expose] public section

open Set

variable {α β : Type*}

section Preorder

variable [Preorder α] [Preorder β]

section

variable {s : Set α} {t : Set β}

/-
**IsUpperSet.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.prod (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ×ˢ
 t)
参数：hs : IsUpperSet s；ht : IsUpperSet t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsUpperSet.prod (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ×ˢ t) :=
  fun _ _ h ha => ⟨hs h.1 ha.1, ht h.2 ha.2⟩
/-
**IsLowerSet.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLowerSet.prod (hs : IsLowerSet s) (ht : IsLowerSet t) : IsLowerSet (s ×ˢ
 t)
参数：hs : IsLowerSet s；ht : IsLowerSet t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsLowerSet.prod (hs : IsLowerSet s) (ht : IsLowerSet t) : IsLowerSet (s ×ˢ t) :=
  fun _ _ h ha => ⟨hs h.1 ha.1, ht h.2 ha.2⟩

end

namespace UpperSet

variable (s s₁ s₂ : UpperSet α) (t t₁ t₂ : UpperSet β) {x : α × β}

/-- The product of two upper sets as an upper set. -/
/-
**UpperSet.prod** 是 Mathlib 中的一个定义，位于命名空间 `UpperSet`。
形式化陈述：prod : UpperSet (α × β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two upper sets as an upper set.
-/
def prod : UpperSet (α × β) :=
  ⟨s ×ˢ t, s.2.prod t.2⟩
/-
**UpperSet.instSProd** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
形式化陈述：instSProd : SProd (UpperSet α) (UpperSet β) (UpperSet (α × β)) where sprod
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSProd : SProd (UpperSet α) (UpperSet β) (UpperSet (α × β)) where
  sprod := UpperSet.prod

@[simp, norm_cast]
/-
**UpperSet.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_prod : ((s ×ˢ t : UpperSet (α × β)) : Set (α × β)) = (s : Set α) ×ˢ t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod : ((s ×ˢ t : UpperSet (α × β)) : Set (α × β)) = (s : Set α) ×ˢ t :=
  rfl

@[simp]
/-
**UpperSet.mem_prod** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：mem_prod {s : UpperSet α} {t : UpperSet β} : x in s ×ˢ t ↔ x.1 in s ∧ x.2 
in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_prod {s : UpperSet α} {t : UpperSet β} : x ∈ s ×ˢ t ↔ x.1 ∈ s ∧ x.2 ∈ t :=
  Iff.rfl
/-
**UpperSet.Ici_prod** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：Ici_prod (x : α × β) : Ici x = Ici x.1 ×ˢ Ici x.2
参数：x : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ici_prod (x : α × β) : Ici x = Ici x.1 ×ˢ Ici x.2 :=
  rfl

@[simp]
/-
**UpperSet.Ici_prod_Ici** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：Ici_prod_Ici (a : α) (b : β) : Ici a ×ˢ Ici b = Ici (a, b)
参数：a : α；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ici_prod_Ici (a : α) (b : β) : Ici a ×ˢ Ici b = Ici (a, b) :=
  rfl

@[simp]
/-
**UpperSet.prod_top** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：prod_top : s ×ˢ (⊤ : UpperSet β) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSet.ext`：ext {s t : UpperSet α} : (s : Set α) = t -> s = t
· 使用定理 `Set.prod_empty`：prod_empty : s ×ˢ (∅ : Set β) = ∅
-/
theorem prod_top : s ×ˢ (⊤ : UpperSet β) = ⊤ :=
  ext prod_empty

@[simp]
/-
**UpperSet.top_prod** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：top_prod : (⊤ : UpperSet α) ×ˢ t = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSet.ext`：ext {s t : UpperSet α} : (s : Set α) = t -> s = t
· 使用定理 `Set.empty_prod`：empty_prod : (∅ : Set α) ×ˢ t = ∅
-/
theorem top_prod : (⊤ : UpperSet α) ×ˢ t = ⊤ :=
  ext empty_prod

@[simp]
/-
**UpperSet.bot_prod_bot** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：bot_prod_bot : (⊥ : UpperSet α) ×ˢ (⊥ : UpperSet β) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSet.ext`：ext {s t : UpperSet α} : (s : Set α) = t -> s = t
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
-/
theorem bot_prod_bot : (⊥ : UpperSet α) ×ˢ (⊥ : UpperSet β) = ⊥ :=
  ext univ_prod_univ

@[simp]
/-
**UpperSet.sup_prod** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：sup_prod : (s₁ ⊔ s₂) ×ˢ t = s₁ ×ˢ t ⊔ s₂ ×ˢ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSet.ext`：ext {s t : UpperSet α} : (s : Set α) = t -> s = t
· 使用定理 `Set.inter_prod`：inter_prod : (s₁ inter s₂) ×ˢ t = s₁ ×ˢ t inter s₂ ×ˢ t
-/
theorem sup_prod : (s₁ ⊔ s₂) ×ˢ t = s₁ ×ˢ t ⊔ s₂ ×ˢ t :=
  ext inter_prod

@[simp]
/-
**UpperSet.prod_sup** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：prod_sup : s ×ˢ (t₁ ⊔ t₂) = s ×ˢ t₁ ⊔ s ×ˢ t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSet.ext`：ext {s t : UpperSet α} : (s : Set α) = t -> s = t
· 使用定理 `Set.prod_inter`：prod_inter : s ×ˢ (t₁ inter t₂) = s ×ˢ t₁ inter s ×ˢ t₂
-/
theorem prod_sup : s ×ˢ (t₁ ⊔ t₂) = s ×ˢ t₁ ⊔ s ×ˢ t₂ :=
  ext prod_inter

@[simp]
/-
**UpperSet.inf_prod** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：inf_prod : (s₁ ⊓ s₂) ×ˢ t = s₁ ×ˢ t ⊓ s₂ ×ˢ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSet.ext`：ext {s t : UpperSet α} : (s : Set α) = t -> s = t
· 使用定理 `Set.union_prod`：union_prod : (s₁ union s₂) ×ˢ t = s₁ ×ˢ t union s₂ ×ˢ t
-/
theorem inf_prod : (s₁ ⊓ s₂) ×ˢ t = s₁ ×ˢ t ⊓ s₂ ×ˢ t :=
  ext union_prod

@[simp]
/-
**UpperSet.prod_inf** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：prod_inf : s ×ˢ (t₁ ⊓ t₂) = s ×ˢ t₁ ⊓ s ×ˢ t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSet.ext`：ext {s t : UpperSet α} : (s : Set α) = t -> s = t
· 使用定理 `Set.prod_union`：prod_union : s ×ˢ (t₁ union t₂) = s ×ˢ t₁ union s ×ˢ t₂
-/
theorem prod_inf : s ×ˢ (t₁ ⊓ t₂) = s ×ˢ t₁ ⊓ s ×ˢ t₂ :=
  ext prod_union
/-
**UpperSet.prod_sup_prod** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：prod_sup_prod : s₁ ×ˢ t₁ ⊔ s₂ ×ˢ t₂ = (s₁ ⊔ s₂) ×ˢ (t₁ ⊔ t₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSet.ext`：ext {s t : UpperSet α} : (s : Set α) = t -> s = t
· 使用定理 `Set.prod_inter_prod`：prod_inter_prod : s₁ ×ˢ t₁ inter s₂ ×ˢ t₂ = (s₁ int
er s₂) ×ˢ (t₁ inter t₂)
-/
theorem prod_sup_prod : s₁ ×ˢ t₁ ⊔ s₂ ×ˢ t₂ = (s₁ ⊔ s₂) ×ˢ (t₁ ⊔ t₂) :=
  ext prod_inter_prod

variable {s s₁ s₂ t t₁ t₂}

@[gcongr, mono]
/-
**UpperSet.prod_mono** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：prod_mono : s₁ <= s₂ -> t₁ <= t₂ -> s₁ ×ˢ t₁ <= s₂ ×ˢ t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
-/
theorem prod_mono : s₁ ≤ s₂ → t₁ ≤ t₂ → s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ :=
  Set.prod_mono
/-
**UpperSet.prod_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：prod_mono_left : s₁ <= s₂ -> s₁ ×ˢ t <= s₂ ×ˢ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_mono_left`：prod_mono_left (hs : s₁ subseteq s₂) : s₁ ×ˢ t subse
teq s₂ ×ˢ t
-/
theorem prod_mono_left : s₁ ≤ s₂ → s₁ ×ˢ t ≤ s₂ ×ˢ t :=
  Set.prod_mono_left
/-
**UpperSet.prod_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：prod_mono_right : t₁ <= t₂ -> s ×ˢ t₁ <= s ×ˢ t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_mono_right`：prod_mono_right (ht : t₁ subseteq t₂) : s ×ˢ t₁ sub
seteq s ×ˢ t₂
-/
theorem prod_mono_right : t₁ ≤ t₂ → s ×ˢ t₁ ≤ s ×ˢ t₂ :=
  Set.prod_mono_right

@[simp]
/-
**UpperSet.prod_self_le_prod_self** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：prod_self_le_prod_self : s₁ ×ˢ s₁ <= s₂ ×ˢ s₂ ↔ s₁ <= s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_self_subset_prod_self`：prod_self_subset_prod_self : s₁ ×ˢ s₁ su
bseteq s₂ ×ˢ s₂ ↔ s₁ subseteq s₂
-/
theorem prod_self_le_prod_self : s₁ ×ˢ s₁ ≤ s₂ ×ˢ s₂ ↔ s₁ ≤ s₂ :=
  prod_self_subset_prod_self

@[simp]
/-
**UpperSet.prod_self_lt_prod_self** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：prod_self_lt_prod_self : s₁ ×ˢ s₁ < s₂ ×ˢ s₂ ↔ s₁ < s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_self_ssubset_prod_self`：prod_self_ssubset_prod_self : s₁ ×ˢ s₁ 
⊂ s₂ ×ˢ s₂ ↔ s₁ ⊂ s₂
-/
theorem prod_self_lt_prod_self : s₁ ×ˢ s₁ < s₂ ×ˢ s₂ ↔ s₁ < s₂ :=
  prod_self_ssubset_prod_self
/-
**UpperSet.prod_le_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：prod_le_prod_iff : s₁ ×ˢ t₁ <= s₂ ×ˢ t₂ ↔ s₁ <= s₂ ∧ t₁ <= t₂ ∨ s₂ = ⊤ ∨ t
₂ = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.prod_subset_prod_iff`：prod_subset_prod_iff : s ×ˢ t subseteq s₁ ×ˢ t
₁ ↔ s subseteq s₁ ∧ t subseteq t₁ ∨ s = ∅ ∨ t = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_le_prod_iff : s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ ↔ s₁ ≤ s₂ ∧ t₁ ≤ t₂ ∨ s₂ = ⊤ ∨ t₂ = ⊤ :=
  prod_subset_prod_iff.trans <| by simp

@[simp]
/-
**UpperSet.prod_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：prod_eq_top : s ×ˢ t = ⊤ ↔ s = ⊤ ∨ t = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.prod_eq_empty_iff`：prod_eq_empty_iff : s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅
-/
theorem prod_eq_top : s ×ˢ t = ⊤ ↔ s = ⊤ ∨ t = ⊤ := by
  simp_rw [SetLike.ext'_iff]
  exact prod_eq_empty_iff

@[simp]
/-
**UpperSet.codisjoint_prod** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：codisjoint_prod : Codisjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Codisjoint s₁ s₂ ∨ Co
disjoint t₁ t₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `UpperSet.prod_sup_prod`：prod_sup_prod : s₁ ×ˢ t₁ ⊔ s₂ ×ˢ t₂ = (s₁ ⊔ s₂) 
×ˢ (t₁ ⊔ t₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem codisjoint_prod :
    Codisjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Codisjoint s₁ s₂ ∨ Codisjoint t₁ t₂ := by
  simp_rw [codisjoint_iff, prod_sup_prod, prod_eq_top]

end UpperSet

namespace LowerSet

variable (s s₁ s₂ : LowerSet α) (t t₁ t₂ : LowerSet β) {x : α × β}

/-- The product of two lower sets as a lower set. -/
/-
**LowerSet.prod** 是 Mathlib 中的一个定义，位于命名空间 `LowerSet`。
形式化陈述：prod : LowerSet (α × β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two lower sets as a lower set.
-/
def prod : LowerSet (α × β) := ⟨s ×ˢ t, s.2.prod t.2⟩
/-
**LowerSet.instSProd** 是 Mathlib 中的一个实例，位于命名空间 `LowerSet`。
形式化陈述：instSProd : SProd (LowerSet α) (LowerSet β) (LowerSet (α × β)) where sprod
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSProd : SProd (LowerSet α) (LowerSet β) (LowerSet (α × β)) where
  sprod := LowerSet.prod

@[simp, norm_cast]
/-
**LowerSet.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：coe_prod : ((s ×ˢ t : LowerSet (α × β)) : Set (α × β)) = (s : Set α) ×ˢ t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod : ((s ×ˢ t : LowerSet (α × β)) : Set (α × β)) = (s : Set α) ×ˢ t := rfl

@[simp]
/-
**LowerSet.mem_prod** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：mem_prod {s : LowerSet α} {t : LowerSet β} : x in s ×ˢ t ↔ x.1 in s ∧ x.2 
in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_prod {s : LowerSet α} {t : LowerSet β} : x ∈ s ×ˢ t ↔ x.1 ∈ s ∧ x.2 ∈ t :=
  Iff.rfl
/-
**LowerSet.Iic_prod** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：Iic_prod (x : α × β) : Iic x = Iic x.1 ×ˢ Iic x.2
参数：x : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iic_prod (x : α × β) : Iic x = Iic x.1 ×ˢ Iic x.2 :=
  rfl

@[simp]
/-
**LowerSet.Ici_prod_Ici** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：Ici_prod_Ici (a : α) (b : β) : Iic a ×ˢ Iic b = Iic (a, b)
参数：a : α；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ici_prod_Ici (a : α) (b : β) : Iic a ×ˢ Iic b = Iic (a, b) :=
  rfl

@[simp]
/-
**LowerSet.prod_bot** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：prod_bot : s ×ˢ (⊥ : LowerSet β) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSet.ext`：∀ {α : Type u_1} [inst : LE α] {s t : LowerSet α}, ↑s = ↑t
 → s = t
· 使用定理 `Set.prod_empty`：prod_empty : s ×ˢ (∅ : Set β) = ∅
-/
theorem prod_bot : s ×ˢ (⊥ : LowerSet β) = ⊥ :=
  ext prod_empty

@[simp]
/-
**LowerSet.bot_prod** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：bot_prod : (⊥ : LowerSet α) ×ˢ t = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSet.ext`：∀ {α : Type u_1} [inst : LE α] {s t : LowerSet α}, ↑s = ↑t
 → s = t
· 使用定理 `Set.empty_prod`：empty_prod : (∅ : Set α) ×ˢ t = ∅
-/
theorem bot_prod : (⊥ : LowerSet α) ×ˢ t = ⊥ :=
  ext empty_prod

@[simp]
/-
**LowerSet.top_prod_top** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：top_prod_top : (⊤ : LowerSet α) ×ˢ (⊤ : LowerSet β) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSet.ext`：∀ {α : Type u_1} [inst : LE α] {s t : LowerSet α}, ↑s = ↑t
 → s = t
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
-/
theorem top_prod_top : (⊤ : LowerSet α) ×ˢ (⊤ : LowerSet β) = ⊤ :=
  ext univ_prod_univ

@[simp]
/-
**LowerSet.inf_prod** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：inf_prod : (s₁ ⊓ s₂) ×ˢ t = s₁ ×ˢ t ⊓ s₂ ×ˢ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSet.ext`：∀ {α : Type u_1} [inst : LE α] {s t : LowerSet α}, ↑s = ↑t
 → s = t
· 使用定理 `Set.inter_prod`：inter_prod : (s₁ inter s₂) ×ˢ t = s₁ ×ˢ t inter s₂ ×ˢ t
-/
theorem inf_prod : (s₁ ⊓ s₂) ×ˢ t = s₁ ×ˢ t ⊓ s₂ ×ˢ t :=
  ext inter_prod

@[simp]
/-
**LowerSet.prod_inf** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：prod_inf : s ×ˢ (t₁ ⊓ t₂) = s ×ˢ t₁ ⊓ s ×ˢ t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSet.ext`：∀ {α : Type u_1} [inst : LE α] {s t : LowerSet α}, ↑s = ↑t
 → s = t
· 使用定理 `Set.prod_inter`：prod_inter : s ×ˢ (t₁ inter t₂) = s ×ˢ t₁ inter s ×ˢ t₂
-/
theorem prod_inf : s ×ˢ (t₁ ⊓ t₂) = s ×ˢ t₁ ⊓ s ×ˢ t₂ :=
  ext prod_inter

@[simp]
/-
**LowerSet.sup_prod** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：sup_prod : (s₁ ⊔ s₂) ×ˢ t = s₁ ×ˢ t ⊔ s₂ ×ˢ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSet.ext`：∀ {α : Type u_1} [inst : LE α] {s t : LowerSet α}, ↑s = ↑t
 → s = t
· 使用定理 `Set.union_prod`：union_prod : (s₁ union s₂) ×ˢ t = s₁ ×ˢ t union s₂ ×ˢ t
-/
theorem sup_prod : (s₁ ⊔ s₂) ×ˢ t = s₁ ×ˢ t ⊔ s₂ ×ˢ t :=
  ext union_prod

@[simp]
/-
**LowerSet.prod_sup** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：prod_sup : s ×ˢ (t₁ ⊔ t₂) = s ×ˢ t₁ ⊔ s ×ˢ t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSet.ext`：∀ {α : Type u_1} [inst : LE α] {s t : LowerSet α}, ↑s = ↑t
 → s = t
· 使用定理 `Set.prod_union`：prod_union : s ×ˢ (t₁ union t₂) = s ×ˢ t₁ union s ×ˢ t₂
-/
theorem prod_sup : s ×ˢ (t₁ ⊔ t₂) = s ×ˢ t₁ ⊔ s ×ˢ t₂ :=
  ext prod_union
/-
**LowerSet.prod_inf_prod** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：prod_inf_prod : s₁ ×ˢ t₁ ⊓ s₂ ×ˢ t₂ = (s₁ ⊓ s₂) ×ˢ (t₁ ⊓ t₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSet.ext`：∀ {α : Type u_1} [inst : LE α] {s t : LowerSet α}, ↑s = ↑t
 → s = t
· 使用定理 `Set.prod_inter_prod`：prod_inter_prod : s₁ ×ˢ t₁ inter s₂ ×ˢ t₂ = (s₁ int
er s₂) ×ˢ (t₁ inter t₂)
-/
theorem prod_inf_prod : s₁ ×ˢ t₁ ⊓ s₂ ×ˢ t₂ = (s₁ ⊓ s₂) ×ˢ (t₁ ⊓ t₂) :=
  ext prod_inter_prod

variable {s s₁ s₂ t t₁ t₂}
/-
**LowerSet.prod_mono** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：prod_mono : s₁ <= s₂ -> t₁ <= t₂ -> s₁ ×ˢ t₁ <= s₂ ×ˢ t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
-/
theorem prod_mono : s₁ ≤ s₂ → t₁ ≤ t₂ → s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ := Set.prod_mono
/-
**LowerSet.prod_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：prod_mono_left : s₁ <= s₂ -> s₁ ×ˢ t <= s₂ ×ˢ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_mono_left`：prod_mono_left (hs : s₁ subseteq s₂) : s₁ ×ˢ t subse
teq s₂ ×ˢ t
-/
theorem prod_mono_left : s₁ ≤ s₂ → s₁ ×ˢ t ≤ s₂ ×ˢ t := Set.prod_mono_left
/-
**LowerSet.prod_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：prod_mono_right : t₁ <= t₂ -> s ×ˢ t₁ <= s ×ˢ t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_mono_right`：prod_mono_right (ht : t₁ subseteq t₂) : s ×ˢ t₁ sub
seteq s ×ˢ t₂
-/
theorem prod_mono_right : t₁ ≤ t₂ → s ×ˢ t₁ ≤ s ×ˢ t₂ := Set.prod_mono_right

@[simp]
/-
**LowerSet.prod_self_le_prod_self** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：prod_self_le_prod_self : s₁ ×ˢ s₁ <= s₂ ×ˢ s₂ ↔ s₁ <= s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_self_subset_prod_self`：prod_self_subset_prod_self : s₁ ×ˢ s₁ su
bseteq s₂ ×ˢ s₂ ↔ s₁ subseteq s₂
-/
theorem prod_self_le_prod_self : s₁ ×ˢ s₁ ≤ s₂ ×ˢ s₂ ↔ s₁ ≤ s₂ :=
  prod_self_subset_prod_self

@[simp]
/-
**LowerSet.prod_self_lt_prod_self** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：prod_self_lt_prod_self : s₁ ×ˢ s₁ < s₂ ×ˢ s₂ ↔ s₁ < s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_self_ssubset_prod_self`：prod_self_ssubset_prod_self : s₁ ×ˢ s₁ 
⊂ s₂ ×ˢ s₂ ↔ s₁ ⊂ s₂
-/
theorem prod_self_lt_prod_self : s₁ ×ˢ s₁ < s₂ ×ˢ s₂ ↔ s₁ < s₂ :=
  prod_self_ssubset_prod_self
/-
**LowerSet.prod_le_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：prod_le_prod_iff : s₁ ×ˢ t₁ <= s₂ ×ˢ t₂ ↔ s₁ <= s₂ ∧ t₁ <= t₂ ∨ s₁ = ⊥ ∨ t
₁ = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.prod_subset_prod_iff`：prod_subset_prod_iff : s ×ˢ t subseteq s₁ ×ˢ t
₁ ↔ s subseteq s₁ ∧ t subseteq t₁ ∨ s = ∅ ∨ t = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_le_prod_iff : s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ ↔ s₁ ≤ s₂ ∧ t₁ ≤ t₂ ∨ s₁ = ⊥ ∨ t₁ = ⊥ :=
  prod_subset_prod_iff.trans <| by simp

@[simp]
/-
**LowerSet.prod_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：prod_eq_bot : s ×ˢ t = ⊥ ↔ s = ⊥ ∨ t = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.prod_eq_empty_iff`：prod_eq_empty_iff : s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅
-/
theorem prod_eq_bot : s ×ˢ t = ⊥ ↔ s = ⊥ ∨ t = ⊥ := by
  simp_rw [SetLike.ext'_iff]
  exact prod_eq_empty_iff

@[simp]
/-
**LowerSet.disjoint_prod** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：disjoint_prod : Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Disjoint s₁ s₂ ∨ Disjoint
 t₁ t₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LowerSet.prod_inf_prod`：prod_inf_prod : s₁ ×ˢ t₁ ⊓ s₂ ×ˢ t₂ = (s₁ ⊓ s₂) 
×ˢ (t₁ ⊓ t₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_prod : Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Disjoint s₁ s₂ ∨ Disjoint t₁ t₂ := by
  simp_rw [disjoint_iff, prod_inf_prod, prod_eq_bot]

end LowerSet

@[simp]
/-
**upperClosure_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperClosure_prod (s : Set α) (t : Set β) : upperClosure (s ×ˢ t) = upperC
losure s ×ˢ upperClosure t
参数：s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSet.ext`：ext {s t : UpperSet α} : (s : Set α) = t -> s = t
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_and_and_comm`：∀ {a b c d : Prop}, (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem upperClosure_prod (s : Set α) (t : Set β) :
    upperClosure (s ×ˢ t) = upperClosure s ×ˢ upperClosure t := by
  ext
  simp [Prod.le_def, @and_and_and_comm _ (_ ∈ t)]

@[simp]
/-
**lowerClosure_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerClosure_prod (s : Set α) (t : Set β) : lowerClosure (s ×ˢ t) = lowerC
losure s ×ˢ lowerClosure t
参数：s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSet.ext`：∀ {α : Type u_1} [inst : LE α] {s t : LowerSet α}, ↑s = ↑t
 → s = t
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_and_and_comm`：∀ {a b c d : Prop}, (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lowerClosure_prod (s : Set α) (t : Set β) :
    lowerClosure (s ×ˢ t) = lowerClosure s ×ˢ lowerClosure t := by
  ext
  simp [Prod.le_def, @and_and_and_comm _ (_ ∈ t)]

end Preorder

