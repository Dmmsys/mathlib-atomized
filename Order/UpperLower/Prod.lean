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

/--
theorem `IsUpperSet.prod` / 定理 `IsUpperSet.prod`

English:
theorem IsUpperSet.prod
  given: (hs : IsUpperSet s) (ht : IsUpperSet t)
  statement: IsUpperSet (s ×ˢ t)
  proof: fun _ _ h ha => ⟨hs h.1 ha.1, ht h.2 ha.2⟩

中文:
定理 是上集.乘积
  条件: (hs : 是上集 s) (ht : 是上集 t)
  结论: 是上集 (s ×ˢ t)
  证明: fun _ _ h ha => ⟨hs h.1 ha.1, ht h.2 ha.2⟩
-/
theorem IsUpperSet.prod (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ×ˢ t) :=
  fun _ _ h ha => ⟨hs h.1 ha.1, ht h.2 ha.2⟩

/--
theorem `IsLowerSet.prod` / 定理 `IsLowerSet.prod`

English:
theorem IsLowerSet.prod
  given: (hs : IsLowerSet s) (ht : IsLowerSet t)
  statement: IsLowerSet (s ×ˢ t)
  proof: fun _ _ h ha => ⟨hs h.1 ha.1, ht h.2 ha.2⟩

中文:
定理 是下集.乘积
  条件: (hs : 是下集 s) (ht : 是下集 t)
  结论: 是下集 (s ×ˢ t)
  证明: fun _ _ h ha => ⟨hs h.1 ha.1, ht h.2 ha.2⟩
-/
theorem IsLowerSet.prod (hs : IsLowerSet s) (ht : IsLowerSet t) : IsLowerSet (s ×ˢ t) :=
  fun _ _ h ha => ⟨hs h.1 ha.1, ht h.2 ha.2⟩

end

namespace UpperSet

variable (s s₁ s₂ : UpperSet α) (t t₁ t₂ : UpperSet β) {x : α × β}

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: : UpperSet (α × β)
  body: ⟨s ×ˢ t, s.2.prod t.2⟩

中文:
定义 乘积
  签名: : 上集 (α × β)
  定义体: ⟨s ×ˢ t, s.2.prod t.2⟩
-/
def prod : UpperSet (α × β) :=
  ⟨s ×ˢ t, s.2.prod t.2⟩

/--
Instance `instSProd` / 实例 `instSProd`

English:
instance instSProd
  signature: : SProd (UpperSet α) (UpperSet β) (UpperSet (α × β)) where
  body: UpperSet.prod

@[simp, norm_cast]

中文:
实例 instSProd
  签名: : SProd (上集 α) (上集 β) (上集 (α × β)) where
  定义体: UpperSet.prod

@[simp, norm_cast]

Depends on / 依赖: UpperSet, UpperSet.prod
-/
instance instSProd : SProd (UpperSet α) (UpperSet β) (UpperSet (α × β)) where
  sprod := UpperSet.prod

@[simp, norm_cast]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  statement: ((s ×ˢ t : UpperSet (α × β)) : Set (α × β)) = (s : Set α) ×ˢ t
  proof: rfl

@[simp]

中文:
定理 coe_prod
  结论: ((s ×ˢ t : 上集 (α × β)) : 集合 (α × β)) = (s : 集合 α) ×ˢ t
  证明: rfl

@[simp]
-/
theorem coe_prod : ((s ×ˢ t : UpperSet (α × β)) : Set (α × β)) = (s : Set α) ×ˢ t :=
  rfl

@[simp]
/--
theorem `mem_prod` / 定理 `mem_prod`

English:
theorem mem_prod
  given: {s : UpperSet α} {t : UpperSet β}
  statement: x in s ×ˢ t ↔ x.1 in s ∧ x.2 in t
  proof: Iff.rfl

中文:
定理 mem_prod
  条件: {s : 上集 α} {t : 上集 β}
  结论: x in s ×ˢ t ↔ x.1 in s ∧ x.2 in t
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_prod {s : UpperSet α} {t : UpperSet β} : x in s ×ˢ t ↔ x.1 in s ∧ x.2 in t :=
  Iff.rfl

/--
theorem `Ici_prod` / 定理 `Ici_prod`

English:
theorem Ici_prod
  given: (x : α × β)
  statement: Ici x = Ici x.1 ×ˢ Ici x.2
  proof: rfl

@[simp]

中文:
定理 Ici_prod
  条件: (x : α × β)
  结论: 左闭右无界区间 x = 左闭右无界区间 x.1 ×ˢ 左闭右无界区间 x.2
  证明: rfl

@[simp]
-/
theorem Ici_prod (x : α × β) : Ici x = Ici x.1 ×ˢ Ici x.2 :=
  rfl

@[simp]
/--
theorem `Ici_prod_Ici` / 定理 `Ici_prod_Ici`

English:
theorem Ici_prod_Ici
  given: (a : α) (b : β)
  statement: Ici a ×ˢ Ici b = Ici (a, b)
  proof: rfl

@[simp]

中文:
定理 Ici_prod_Ici
  条件: (a : α) (b : β)
  结论: 左闭右无界区间 a ×ˢ 左闭右无界区间 b = 左闭右无界区间 (a, b)
  证明: rfl

@[simp]
-/
theorem Ici_prod_Ici (a : α) (b : β) : Ici a ×ˢ Ici b = Ici (a, b) :=
  rfl

@[simp]
/--
theorem `prod_top` / 定理 `prod_top`

English:
theorem prod_top
  statement: s ×ˢ (⊤ : UpperSet β) = ⊤
  proof: ext prod_empty

@[simp]

中文:
定理 prod_top
  结论: s ×ˢ (⊤ : 上集 β) = ⊤
  证明: ext prod_empty

@[simp]

Depends on / 依赖: prod_empty
-/
theorem prod_top : s ×ˢ (⊤ : UpperSet β) = ⊤ :=
  ext prod_empty

@[simp]
/--
theorem `top_prod` / 定理 `top_prod`

English:
theorem top_prod
  statement: (⊤ : UpperSet α) ×ˢ t = ⊤
  proof: ext empty_prod

@[simp]

中文:
定理 top_prod
  结论: (⊤ : 上集 α) ×ˢ t = ⊤
  证明: ext empty_prod

@[simp]

Depends on / 依赖: empty_prod
-/
theorem top_prod : (⊤ : UpperSet α) ×ˢ t = ⊤ :=
  ext empty_prod

@[simp]
/--
theorem `bot_prod_bot` / 定理 `bot_prod_bot`

English:
theorem bot_prod_bot
  statement: (⊥ : UpperSet α) ×ˢ (⊥ : UpperSet β) = ⊥
  proof: ext univ_prod_univ

@[simp]

中文:
定理 bot_prod_bot
  结论: (⊥ : 上集 α) ×ˢ (⊥ : 上集 β) = ⊥
  证明: ext univ_prod_univ

@[simp]

Depends on / 依赖: univ_prod_univ
-/
theorem bot_prod_bot : (⊥ : UpperSet α) ×ˢ (⊥ : UpperSet β) = ⊥ :=
  ext univ_prod_univ

@[simp]
/--
theorem `sup_prod` / 定理 `sup_prod`

English:
theorem sup_prod
  statement: (s₁ ⊔ s₂) ×ˢ t = s₁ ×ˢ t ⊔ s₂ ×ˢ t
  proof: ext inter_prod

@[simp]

中文:
定理 sup_prod
  结论: (s₁ ⊔ s₂) ×ˢ t = s₁ ×ˢ t ⊔ s₂ ×ˢ t
  证明: ext inter_prod

@[simp]

Depends on / 依赖: inter_prod
-/
theorem sup_prod : (s₁ ⊔ s₂) ×ˢ t = s₁ ×ˢ t ⊔ s₂ ×ˢ t :=
  ext inter_prod

@[simp]
/--
theorem `prod_sup` / 定理 `prod_sup`

English:
theorem prod_sup
  statement: s ×ˢ (t₁ ⊔ t₂) = s ×ˢ t₁ ⊔ s ×ˢ t₂
  proof: ext prod_inter

@[simp]

中文:
定理 prod_sup
  结论: s ×ˢ (t₁ ⊔ t₂) = s ×ˢ t₁ ⊔ s ×ˢ t₂
  证明: ext prod_inter

@[simp]

Depends on / 依赖: prod_inter
-/
theorem prod_sup : s ×ˢ (t₁ ⊔ t₂) = s ×ˢ t₁ ⊔ s ×ˢ t₂ :=
  ext prod_inter

@[simp]
/--
theorem `inf_prod` / 定理 `inf_prod`

English:
theorem inf_prod
  statement: (s₁ ⊓ s₂) ×ˢ t = s₁ ×ˢ t ⊓ s₂ ×ˢ t
  proof: ext union_prod

@[simp]

中文:
定理 inf_prod
  结论: (s₁ ⊓ s₂) ×ˢ t = s₁ ×ˢ t ⊓ s₂ ×ˢ t
  证明: ext union_prod

@[simp]

Depends on / 依赖: union_prod
-/
theorem inf_prod : (s₁ ⊓ s₂) ×ˢ t = s₁ ×ˢ t ⊓ s₂ ×ˢ t :=
  ext union_prod

@[simp]
/--
theorem `prod_inf` / 定理 `prod_inf`

English:
theorem prod_inf
  statement: s ×ˢ (t₁ ⊓ t₂) = s ×ˢ t₁ ⊓ s ×ˢ t₂
  proof: ext prod_union

中文:
定理 prod_inf
  结论: s ×ˢ (t₁ ⊓ t₂) = s ×ˢ t₁ ⊓ s ×ˢ t₂
  证明: ext prod_union

Depends on / 依赖: prod_union
-/
theorem prod_inf : s ×ˢ (t₁ ⊓ t₂) = s ×ˢ t₁ ⊓ s ×ˢ t₂ :=
  ext prod_union

/--
theorem `prod_sup_prod` / 定理 `prod_sup_prod`

English:
theorem prod_sup_prod
  statement: s₁ ×ˢ t₁ ⊔ s₂ ×ˢ t₂ = (s₁ ⊔ s₂) ×ˢ (t₁ ⊔ t₂)
  proof: ext prod_inter_prod

中文:
定理 prod_sup_prod
  结论: s₁ ×ˢ t₁ ⊔ s₂ ×ˢ t₂ = (s₁ ⊔ s₂) ×ˢ (t₁ ⊔ t₂)
  证明: ext prod_inter_prod

Depends on / 依赖: prod_inter_prod
-/
theorem prod_sup_prod : s₁ ×ˢ t₁ ⊔ s₂ ×ˢ t₂ = (s₁ ⊔ s₂) ×ˢ (t₁ ⊔ t₂) :=
  ext prod_inter_prod

variable {s s₁ s₂ t t₁ t₂}

@[gcongr, mono]
/--
theorem `prod_mono` / 定理 `prod_mono`

English:
theorem prod_mono
  statement: s₁ <= s₂ -> t₁ <= t₂ -> s₁ ×ˢ t₁ <= s₂ ×ˢ t₂
  proof: Set.prod_mono

中文:
定理 prod_mono
  结论: s₁ <= s₂ -> t₁ <= t₂ -> s₁ ×ˢ t₁ <= s₂ ×ˢ t₂
  证明: Set.prod_mono

Depends on / 依赖: Set.prod_mono, prod_mono
-/
theorem prod_mono : s₁ <= s₂ -> t₁ <= t₂ -> s₁ ×ˢ t₁ <= s₂ ×ˢ t₂ :=
  Set.prod_mono

/--
theorem `prod_mono_left` / 定理 `prod_mono_left`

English:
theorem prod_mono_left
  statement: s₁ <= s₂ -> s₁ ×ˢ t <= s₂ ×ˢ t
  proof: Set.prod_mono_left

中文:
定理 prod_mono_left
  结论: s₁ <= s₂ -> s₁ ×ˢ t <= s₂ ×ˢ t
  证明: Set.prod_mono_left

Depends on / 依赖: Set.prod_mono_left, prod_mono_left
-/
theorem prod_mono_left : s₁ <= s₂ -> s₁ ×ˢ t <= s₂ ×ˢ t :=
  Set.prod_mono_left

/--
theorem `prod_mono_right` / 定理 `prod_mono_right`

English:
theorem prod_mono_right
  statement: t₁ <= t₂ -> s ×ˢ t₁ <= s ×ˢ t₂
  proof: Set.prod_mono_right

@[simp]

中文:
定理 prod_mono_right
  结论: t₁ <= t₂ -> s ×ˢ t₁ <= s ×ˢ t₂
  证明: Set.prod_mono_right

@[simp]

Depends on / 依赖: Set.prod_mono_right, prod_mono_right
-/
theorem prod_mono_right : t₁ <= t₂ -> s ×ˢ t₁ <= s ×ˢ t₂ :=
  Set.prod_mono_right

@[simp]
/--
theorem `prod_self_le_prod_self` / 定理 `prod_self_le_prod_self`

English:
theorem prod_self_le_prod_self
  statement: s₁ ×ˢ s₁ <= s₂ ×ˢ s₂ ↔ s₁ <= s₂
  proof: prod_self_subset_prod_self

@[simp]

中文:
定理 prod_self_le_prod_self
  结论: s₁ ×ˢ s₁ <= s₂ ×ˢ s₂ ↔ s₁ <= s₂
  证明: prod_self_subset_prod_self

@[simp]

Depends on / 依赖: prod_self_subset_prod_self
-/
theorem prod_self_le_prod_self : s₁ ×ˢ s₁ <= s₂ ×ˢ s₂ ↔ s₁ <= s₂ :=
  prod_self_subset_prod_self

@[simp]
/--
theorem `prod_self_lt_prod_self` / 定理 `prod_self_lt_prod_self`

English:
theorem prod_self_lt_prod_self
  statement: s₁ ×ˢ s₁ < s₂ ×ˢ s₂ ↔ s₁ < s₂
  proof: prod_self_ssubset_prod_self

中文:
定理 prod_self_lt_prod_self
  结论: s₁ ×ˢ s₁ < s₂ ×ˢ s₂ ↔ s₁ < s₂
  证明: prod_self_ssubset_prod_self

Depends on / 依赖: prod_self_ssubset_prod_self
-/
theorem prod_self_lt_prod_self : s₁ ×ˢ s₁ < s₂ ×ˢ s₂ ↔ s₁ < s₂ :=
  prod_self_ssubset_prod_self

/--
theorem `prod_le_prod_iff` / 定理 `prod_le_prod_iff`

English:
theorem prod_le_prod_iff
  statement: s₁ ×ˢ t₁ <= s₂ ×ˢ t₂ ↔ s₁ <= s₂ ∧ t₁ <= t₂ ∨ s₂ = ⊤ ∨ t₂ = ⊤
  proof: prod_subset_prod_iff.trans by simp

@[simp]

中文:
定理 prod_le_prod_iff
  结论: s₁ ×ˢ t₁ <= s₂ ×ˢ t₂ ↔ s₁ <= s₂ ∧ t₁ <= t₂ ∨ s₂ = ⊤ ∨ t₂ = ⊤
  证明: prod_subset_prod_iff.trans by simp

@[simp]

Depends on / 依赖: prod_subset_prod_iff, prod_subset_prod_iff.trans
-/
theorem prod_le_prod_iff : s₁ ×ˢ t₁ <= s₂ ×ˢ t₂ ↔ s₁ <= s₂ ∧ t₁ <= t₂ ∨ s₂ = ⊤ ∨ t₂ = ⊤ :=
prod_subset_prod_iff.trans by simp

@[simp]
/--
theorem `prod_eq_top` / 定理 `prod_eq_top`

English:
theorem prod_eq_top
  statement: s ×ˢ t = ⊤ ↔ s = ⊤ ∨ t = ⊤
  proof: by
  simp_rw [SetLike.ext'_iff]
  exact prod_eq_empty_iff

@[simp]

中文:
定理 prod_eq_top
  结论: s ×ˢ t = ⊤ ↔ s = ⊤ ∨ t = ⊤
  证明: by
  simp_rw [SetLike.ext'_iff]
  exact prod_eq_empty_iff

@[simp]

Depends on / 依赖: SetLike, SetLike.ext, _iff, prod_eq_empty_iff, simp_rw
-/
theorem prod_eq_top : s ×ˢ t = ⊤ ↔ s = ⊤ ∨ t = ⊤ := by
  simp_rw [SetLike.ext'_iff]
  exact prod_eq_empty_iff

@[simp]
/--
theorem `codisjoint_prod` / 定理 `codisjoint_prod`

English:
theorem codisjoint_prod
  proof: by
  simp_rw [codisjoint_iff, prod_sup_prod, prod_eq_top]

中文:
定理 codisjoint_prod
  证明: by
  simp_rw [codisjoint_iff, prod_sup_prod, prod_eq_top]

Depends on / 依赖: codisjoint_iff, prod_eq_top, prod_sup_prod, simp_rw
-/
theorem codisjoint_prod :
    Codisjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Codisjoint s₁ s₂ ∨ Codisjoint t₁ t₂ := by
  simp_rw [codisjoint_iff, prod_sup_prod, prod_eq_top]

end UpperSet

namespace LowerSet

variable (s s₁ s₂ : LowerSet α) (t t₁ t₂ : LowerSet β) {x : α × β}

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: : LowerSet (α × β)
  body: ⟨s ×ˢ t, s.2.prod t.2⟩

中文:
定义 乘积
  签名: : 下集 (α × β)
  定义体: ⟨s ×ˢ t, s.2.prod t.2⟩
-/
def prod : LowerSet (α × β) := ⟨s ×ˢ t, s.2.prod t.2⟩

/--
Instance `instSProd` / 实例 `instSProd`

English:
instance instSProd
  signature: : SProd (LowerSet α) (LowerSet β) (LowerSet (α × β)) where
  body: LowerSet.prod

@[simp, norm_cast]

中文:
实例 instSProd
  签名: : SProd (下集 α) (下集 β) (下集 (α × β)) where
  定义体: LowerSet.prod

@[simp, norm_cast]

Depends on / 依赖: LowerSet, LowerSet.prod
-/
instance instSProd : SProd (LowerSet α) (LowerSet β) (LowerSet (α × β)) where
  sprod := LowerSet.prod

@[simp, norm_cast]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  statement: ((s ×ˢ t : LowerSet (α × β)) : Set (α × β)) = (s : Set α) ×ˢ t
  proof: rfl

@[simp]

中文:
定理 coe_prod
  结论: ((s ×ˢ t : 下集 (α × β)) : 集合 (α × β)) = (s : 集合 α) ×ˢ t
  证明: rfl

@[simp]
-/
theorem coe_prod : ((s ×ˢ t : LowerSet (α × β)) : Set (α × β)) = (s : Set α) ×ˢ t := rfl

@[simp]
/--
theorem `mem_prod` / 定理 `mem_prod`

English:
theorem mem_prod
  given: {s : LowerSet α} {t : LowerSet β}
  statement: x in s ×ˢ t ↔ x.1 in s ∧ x.2 in t
  proof: Iff.rfl

中文:
定理 mem_prod
  条件: {s : 下集 α} {t : 下集 β}
  结论: x in s ×ˢ t ↔ x.1 in s ∧ x.2 in t
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_prod {s : LowerSet α} {t : LowerSet β} : x in s ×ˢ t ↔ x.1 in s ∧ x.2 in t :=
  Iff.rfl

/--
theorem `Iic_prod` / 定理 `Iic_prod`

English:
theorem Iic_prod
  given: (x : α × β)
  statement: Iic x = Iic x.1 ×ˢ Iic x.2
  proof: rfl

@[simp]

中文:
定理 Iic_prod
  条件: (x : α × β)
  结论: 左无界右闭区间 x = 左无界右闭区间 x.1 ×ˢ 左无界右闭区间 x.2
  证明: rfl

@[simp]
-/
theorem Iic_prod (x : α × β) : Iic x = Iic x.1 ×ˢ Iic x.2 :=
  rfl

@[simp]
/--
theorem `Ici_prod_Ici` / 定理 `Ici_prod_Ici`

English:
theorem Ici_prod_Ici
  given: (a : α) (b : β)
  statement: Iic a ×ˢ Iic b = Iic (a, b)
  proof: rfl

@[simp]

中文:
定理 Ici_prod_Ici
  条件: (a : α) (b : β)
  结论: 左无界右闭区间 a ×ˢ 左无界右闭区间 b = 左无界右闭区间 (a, b)
  证明: rfl

@[simp]
-/
theorem Ici_prod_Ici (a : α) (b : β) : Iic a ×ˢ Iic b = Iic (a, b) :=
  rfl

@[simp]
/--
theorem `prod_bot` / 定理 `prod_bot`

English:
theorem prod_bot
  statement: s ×ˢ (⊥ : LowerSet β) = ⊥
  proof: ext prod_empty

@[simp]

中文:
定理 prod_bot
  结论: s ×ˢ (⊥ : 下集 β) = ⊥
  证明: ext prod_empty

@[simp]

Depends on / 依赖: prod_empty
-/
theorem prod_bot : s ×ˢ (⊥ : LowerSet β) = ⊥ :=
  ext prod_empty

@[simp]
/--
theorem `bot_prod` / 定理 `bot_prod`

English:
theorem bot_prod
  statement: (⊥ : LowerSet α) ×ˢ t = ⊥
  proof: ext empty_prod

@[simp]

中文:
定理 bot_prod
  结论: (⊥ : 下集 α) ×ˢ t = ⊥
  证明: ext empty_prod

@[simp]

Depends on / 依赖: empty_prod
-/
theorem bot_prod : (⊥ : LowerSet α) ×ˢ t = ⊥ :=
  ext empty_prod

@[simp]
/--
theorem `top_prod_top` / 定理 `top_prod_top`

English:
theorem top_prod_top
  statement: (⊤ : LowerSet α) ×ˢ (⊤ : LowerSet β) = ⊤
  proof: ext univ_prod_univ

@[simp]

中文:
定理 top_prod_top
  结论: (⊤ : 下集 α) ×ˢ (⊤ : 下集 β) = ⊤
  证明: ext univ_prod_univ

@[simp]

Depends on / 依赖: univ_prod_univ
-/
theorem top_prod_top : (⊤ : LowerSet α) ×ˢ (⊤ : LowerSet β) = ⊤ :=
  ext univ_prod_univ

@[simp]
/--
theorem `inf_prod` / 定理 `inf_prod`

English:
theorem inf_prod
  statement: (s₁ ⊓ s₂) ×ˢ t = s₁ ×ˢ t ⊓ s₂ ×ˢ t
  proof: ext inter_prod

@[simp]

中文:
定理 inf_prod
  结论: (s₁ ⊓ s₂) ×ˢ t = s₁ ×ˢ t ⊓ s₂ ×ˢ t
  证明: ext inter_prod

@[simp]

Depends on / 依赖: inter_prod
-/
theorem inf_prod : (s₁ ⊓ s₂) ×ˢ t = s₁ ×ˢ t ⊓ s₂ ×ˢ t :=
  ext inter_prod

@[simp]
/--
theorem `prod_inf` / 定理 `prod_inf`

English:
theorem prod_inf
  statement: s ×ˢ (t₁ ⊓ t₂) = s ×ˢ t₁ ⊓ s ×ˢ t₂
  proof: ext prod_inter

@[simp]

中文:
定理 prod_inf
  结论: s ×ˢ (t₁ ⊓ t₂) = s ×ˢ t₁ ⊓ s ×ˢ t₂
  证明: ext prod_inter

@[simp]

Depends on / 依赖: prod_inter
-/
theorem prod_inf : s ×ˢ (t₁ ⊓ t₂) = s ×ˢ t₁ ⊓ s ×ˢ t₂ :=
  ext prod_inter

@[simp]
/--
theorem `sup_prod` / 定理 `sup_prod`

English:
theorem sup_prod
  statement: (s₁ ⊔ s₂) ×ˢ t = s₁ ×ˢ t ⊔ s₂ ×ˢ t
  proof: ext union_prod

@[simp]

中文:
定理 sup_prod
  结论: (s₁ ⊔ s₂) ×ˢ t = s₁ ×ˢ t ⊔ s₂ ×ˢ t
  证明: ext union_prod

@[simp]

Depends on / 依赖: union_prod
-/
theorem sup_prod : (s₁ ⊔ s₂) ×ˢ t = s₁ ×ˢ t ⊔ s₂ ×ˢ t :=
  ext union_prod

@[simp]
/--
theorem `prod_sup` / 定理 `prod_sup`

English:
theorem prod_sup
  statement: s ×ˢ (t₁ ⊔ t₂) = s ×ˢ t₁ ⊔ s ×ˢ t₂
  proof: ext prod_union

中文:
定理 prod_sup
  结论: s ×ˢ (t₁ ⊔ t₂) = s ×ˢ t₁ ⊔ s ×ˢ t₂
  证明: ext prod_union

Depends on / 依赖: prod_union
-/
theorem prod_sup : s ×ˢ (t₁ ⊔ t₂) = s ×ˢ t₁ ⊔ s ×ˢ t₂ :=
  ext prod_union

/--
theorem `prod_inf_prod` / 定理 `prod_inf_prod`

English:
theorem prod_inf_prod
  statement: s₁ ×ˢ t₁ ⊓ s₂ ×ˢ t₂ = (s₁ ⊓ s₂) ×ˢ (t₁ ⊓ t₂)
  proof: ext prod_inter_prod

中文:
定理 prod_inf_prod
  结论: s₁ ×ˢ t₁ ⊓ s₂ ×ˢ t₂ = (s₁ ⊓ s₂) ×ˢ (t₁ ⊓ t₂)
  证明: ext prod_inter_prod

Depends on / 依赖: prod_inter_prod
-/
theorem prod_inf_prod : s₁ ×ˢ t₁ ⊓ s₂ ×ˢ t₂ = (s₁ ⊓ s₂) ×ˢ (t₁ ⊓ t₂) :=
  ext prod_inter_prod

variable {s s₁ s₂ t t₁ t₂}

/--
theorem `prod_mono` / 定理 `prod_mono`

English:
theorem prod_mono
  statement: s₁ <= s₂ -> t₁ <= t₂ -> s₁ ×ˢ t₁ <= s₂ ×ˢ t₂
  proof: Set.prod_mono

中文:
定理 prod_mono
  结论: s₁ <= s₂ -> t₁ <= t₂ -> s₁ ×ˢ t₁ <= s₂ ×ˢ t₂
  证明: Set.prod_mono

Depends on / 依赖: Set.prod_mono, prod_mono
-/
theorem prod_mono : s₁ <= s₂ -> t₁ <= t₂ -> s₁ ×ˢ t₁ <= s₂ ×ˢ t₂ := Set.prod_mono

/--
theorem `prod_mono_left` / 定理 `prod_mono_left`

English:
theorem prod_mono_left
  statement: s₁ <= s₂ -> s₁ ×ˢ t <= s₂ ×ˢ t
  proof: Set.prod_mono_left

中文:
定理 prod_mono_left
  结论: s₁ <= s₂ -> s₁ ×ˢ t <= s₂ ×ˢ t
  证明: Set.prod_mono_left

Depends on / 依赖: Set.prod_mono_left, prod_mono_left
-/
theorem prod_mono_left : s₁ <= s₂ -> s₁ ×ˢ t <= s₂ ×ˢ t := Set.prod_mono_left

/--
theorem `prod_mono_right` / 定理 `prod_mono_right`

English:
theorem prod_mono_right
  statement: t₁ <= t₂ -> s ×ˢ t₁ <= s ×ˢ t₂
  proof: Set.prod_mono_right

@[simp]

中文:
定理 prod_mono_right
  结论: t₁ <= t₂ -> s ×ˢ t₁ <= s ×ˢ t₂
  证明: Set.prod_mono_right

@[simp]

Depends on / 依赖: Set.prod_mono_right, prod_mono_right
-/
theorem prod_mono_right : t₁ <= t₂ -> s ×ˢ t₁ <= s ×ˢ t₂ := Set.prod_mono_right

@[simp]
/--
theorem `prod_self_le_prod_self` / 定理 `prod_self_le_prod_self`

English:
theorem prod_self_le_prod_self
  statement: s₁ ×ˢ s₁ <= s₂ ×ˢ s₂ ↔ s₁ <= s₂
  proof: prod_self_subset_prod_self

@[simp]

中文:
定理 prod_self_le_prod_self
  结论: s₁ ×ˢ s₁ <= s₂ ×ˢ s₂ ↔ s₁ <= s₂
  证明: prod_self_subset_prod_self

@[simp]

Depends on / 依赖: prod_self_subset_prod_self
-/
theorem prod_self_le_prod_self : s₁ ×ˢ s₁ <= s₂ ×ˢ s₂ ↔ s₁ <= s₂ :=
  prod_self_subset_prod_self

@[simp]
/--
theorem `prod_self_lt_prod_self` / 定理 `prod_self_lt_prod_self`

English:
theorem prod_self_lt_prod_self
  statement: s₁ ×ˢ s₁ < s₂ ×ˢ s₂ ↔ s₁ < s₂
  proof: prod_self_ssubset_prod_self

中文:
定理 prod_self_lt_prod_self
  结论: s₁ ×ˢ s₁ < s₂ ×ˢ s₂ ↔ s₁ < s₂
  证明: prod_self_ssubset_prod_self

Depends on / 依赖: prod_self_ssubset_prod_self
-/
theorem prod_self_lt_prod_self : s₁ ×ˢ s₁ < s₂ ×ˢ s₂ ↔ s₁ < s₂ :=
  prod_self_ssubset_prod_self

/--
theorem `prod_le_prod_iff` / 定理 `prod_le_prod_iff`

English:
theorem prod_le_prod_iff
  statement: s₁ ×ˢ t₁ <= s₂ ×ˢ t₂ ↔ s₁ <= s₂ ∧ t₁ <= t₂ ∨ s₁ = ⊥ ∨ t₁ = ⊥
  proof: prod_subset_prod_iff.trans by simp

@[simp]

中文:
定理 prod_le_prod_iff
  结论: s₁ ×ˢ t₁ <= s₂ ×ˢ t₂ ↔ s₁ <= s₂ ∧ t₁ <= t₂ ∨ s₁ = ⊥ ∨ t₁ = ⊥
  证明: prod_subset_prod_iff.trans by simp

@[simp]

Depends on / 依赖: prod_subset_prod_iff, prod_subset_prod_iff.trans
-/
theorem prod_le_prod_iff : s₁ ×ˢ t₁ <= s₂ ×ˢ t₂ ↔ s₁ <= s₂ ∧ t₁ <= t₂ ∨ s₁ = ⊥ ∨ t₁ = ⊥ :=
prod_subset_prod_iff.trans by simp

@[simp]
/--
theorem `prod_eq_bot` / 定理 `prod_eq_bot`

English:
theorem prod_eq_bot
  statement: s ×ˢ t = ⊥ ↔ s = ⊥ ∨ t = ⊥
  proof: by
  simp_rw [SetLike.ext'_iff]
  exact prod_eq_empty_iff

@[simp]

中文:
定理 prod_eq_bot
  结论: s ×ˢ t = ⊥ ↔ s = ⊥ ∨ t = ⊥
  证明: by
  simp_rw [SetLike.ext'_iff]
  exact prod_eq_empty_iff

@[simp]

Depends on / 依赖: SetLike, SetLike.ext, _iff, instContinuousSMulForall, prod_eq_empty_iff, simp_rw
-/
theorem prod_eq_bot : s ×ˢ t = ⊥ ↔ s = ⊥ ∨ t = ⊥ := by
  simp_rw [SetLike.ext'_iff]
  exact prod_eq_empty_iff

@[simp]
/--
theorem `disjoint_prod` / 定理 `disjoint_prod`

English:
theorem disjoint_prod
  statement: Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Disjoint s₁ s₂ ∨ Disjoint t₁ t₂
  proof: by
  simp_rw [disjoint_iff, prod_inf_prod, prod_eq_bot]

中文:
定理 disjoint_prod
  结论: Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Disjoint s₁ s₂ ∨ Disjoint t₁ t₂
  证明: by
  simp_rw [disjoint_iff, prod_inf_prod, prod_eq_bot]

Depends on / 依赖: disjoint_iff, prod_eq_bot, prod_inf_prod, simp_rw
-/
theorem disjoint_prod : Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Disjoint s₁ s₂ ∨ Disjoint t₁ t₂ := by
  simp_rw [disjoint_iff, prod_inf_prod, prod_eq_bot]

end LowerSet

@[simp]
/--
theorem `upperClosure_prod` / 定理 `upperClosure_prod`

English:
theorem upperClosure_prod
  given: (s : Set α) (t : Set β)
  proof: by
  ext
  simp [Prod.le_def, @and_and_and_comm _ (_ in t)]

@[simp]

中文:
定理 upperClosure_prod
  条件: (s : 集合 α) (t : 集合 β)
  证明: by
  ext
  simp [Prod.le_def, @and_and_and_comm _ (_ in t)]

@[simp]

Depends on / 依赖: Prod.le_def, and_and_and_comm, le_def
-/
theorem upperClosure_prod (s : Set α) (t : Set β) :
    upperClosure (s ×ˢ t) = upperClosure s ×ˢ upperClosure t := by
  ext
  simp [Prod.le_def, @and_and_and_comm _ (_ in t)]

@[simp]
/--
theorem `lowerClosure_prod` / 定理 `lowerClosure_prod`

English:
theorem lowerClosure_prod
  given: (s : Set α) (t : Set β)
  proof: by
  ext
  simp [Prod.le_def, @and_and_and_comm _ (_ in t)]

中文:
定理 lowerClosure_prod
  条件: (s : 集合 α) (t : 集合 β)
  证明: by
  ext
  simp [Prod.le_def, @and_and_and_comm _ (_ in t)]

Depends on / 依赖: Prod.le_def, and_and_and_comm, le_def
-/
theorem lowerClosure_prod (s : Set α) (t : Set β) :
    lowerClosure (s ×ˢ t) = lowerClosure s ×ˢ lowerClosure t := by
  ext
  simp [Prod.le_def, @and_and_and_comm _ (_ in t)]

end Preorder
