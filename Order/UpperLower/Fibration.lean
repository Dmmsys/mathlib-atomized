/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
module

public import Mathlib.Order.UpperLower.Basic

/-!
# Upper/lower sets and fibrations
-/

public section

open Set

namespace Relation

variable {α β : Type*} {f : α → β}

/-
**Relation.Fibration.isLowerSet_image** 是 Mathlib 中的一个定理，位于命名空间 `Relation.Fibrat
ion`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} [inst : LE α] [inst_1 : LE β],
   Relation.Fibration (fun x1 x2 => x1 ≤ x2) (fun x1 x2 => x1 ≤ x2) f → ∀ {s : S
et α}, IsLowerSet s → IsLowerSet (f '' s)
参数：fun x1 x2 => x1 ≤ x2；fun x1 x2 => x1 ≤ x2；f '' s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Fibration.isLowerSet_image [LE α] [LE β] (hf : Fibration (· ≤ ·) (· ≤ ·) f)
    {s : Set α} (hs : IsLowerSet s) : IsLowerSet (f '' s) := by
  rintro _ y' e ⟨x, hx, rfl⟩; obtain ⟨y, e', rfl⟩ := hf e; exact ⟨_, hs e' hx, rfl⟩

alias _root_.IsLowerSet.image_fibration := Fibration.isLowerSet_image
/-
**Relation.fibration_iff_isLowerSet_image_Iic** 是 Mathlib 中的一个引理，位于命名空间 `Relatio
n`。
形式化陈述：fibration_iff_isLowerSet_image_Iic [Preorder α] [LE β] : Fibration (· <= ·
) (· <= ·) f ↔ forall x, IsLowerSet (f '' Iic x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLowerSet.image_fibration`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} 
[inst : LE α] [inst_1 : LE β],   Relation.Fibration (fun x1 x2 => x1 ≤ x2) (fun 
x1 x2 => x1 ≤ x2…
· 使用定理 `isLowerSet_Iic`：∀ {α : Type u_1} [inst : Preorder α] (a : α), IsLowerSet
 (Set.Iic a)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma fibration_iff_isLowerSet_image_Iic [Preorder α] [LE β] :
    Fibration (· ≤ ·) (· ≤ ·) f ↔ ∀ x, IsLowerSet (f '' Iic x) :=
  ⟨fun h x ↦ (isLowerSet_Iic x).image_fibration h, fun H x _ e ↦ H x e ⟨x, le_rfl, rfl⟩⟩
/-
**Relation.fibration_iff_isLowerSet_image** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：fibration_iff_isLowerSet_image [Preorder α] [LE β] : Fibration (· <= ·) (·
 <= ·) f ↔ forall s, IsLowerSet s -> IsLowerSet (f '' s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.Fibration.isLowerSet_image`：∀ {α : Type u_1} {β : Type u_2} {f 
: α → β} [inst : LE α] [inst_1 : LE β],   Relation.Fibration (fun x1 x2 => x1 ≤ 
x2) (fun x1 x2 => x1 ≤ x2…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Relation.fibration_iff_isLowerSet_image_Iic`：fibration_iff_isLowerSet_im
age_Iic [Preorder α] [LE β] : Fibration (· <= ·) (· <= ·) f ↔ forall x, IsLowerS
et (f '' Iic x)
· 使用定理 `isLowerSet_Iic`：∀ {α : Type u_1} [inst : Preorder α] (a : α), IsLowerSet
 (Set.Iic a)
-/
lemma fibration_iff_isLowerSet_image [Preorder α] [LE β] :
    Fibration (· ≤ ·) (· ≤ ·) f ↔ ∀ s, IsLowerSet s → IsLowerSet (f '' s) :=
  ⟨Fibration.isLowerSet_image,
    fun H ↦ fibration_iff_isLowerSet_image_Iic.mpr (H _ <| isLowerSet_Iic ·)⟩
/-
**Relation.fibration_iff_image_Iic** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：fibration_iff_image_Iic [Preorder α] [Preorder β] (hf : Monotone f) : Fibr
ation (· <= ·) (· <= ·) f ↔ forall x, f '' Iic x = Iic (f x)
参数：hf : Monotone f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsLowerSet.Iic_subset`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α},
 IsLowerSet s → ∀ ⦃a : α⦄, a ∈ s → Set.Iic a ⊆ s
· 使用定理 `Relation.Fibration.isLowerSet_image`：∀ {α : Type u_1} {β : Type u_2} {f 
: α → β} [inst : LE α] [inst_1 : LE β],   Relation.Fibration (fun x1 x2 => x1 ≤ 
x2) (fun x1 x2 => x1 ≤ x2…
· 使用定理 `isLowerSet_Iic`：∀ {α : Type u_1} [inst : Preorder α] (a : α), IsLowerSet
 (Set.Iic a)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Relation.fibration_iff_isLowerSet_image_Iic`：fibration_iff_isLowerSet_im
age_Iic [Preorder α] [LE β] : Fibration (· <= ·) (· <= ·) f ↔ forall x, IsLowerS
et (f '' Iic x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma fibration_iff_image_Iic [Preorder α] [Preorder β] (hf : Monotone f) :
    Fibration (· ≤ ·) (· ≤ ·) f ↔ ∀ x, f '' Iic x = Iic (f x) :=
  ⟨fun H x ↦ le_antisymm (fun _ ⟨_, hy, e⟩ ↦ e ▸ hf hy)
    ((H.isLowerSet_image (isLowerSet_Iic x)).Iic_subset ⟨x, le_rfl, rfl⟩),
    fun H ↦ fibration_iff_isLowerSet_image_Iic.mpr (fun x ↦ (H x).symm ▸ isLowerSet_Iic (f x))⟩
/-
**Relation.Fibration.isUpperSet_image** 是 Mathlib 中的一个定理，位于命名空间 `Relation.Fibrat
ion`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} [inst : LE α] [inst_1 : LE β],
   Relation.Fibration (fun x1 x2 => x1 ≥ x2) (fun x1 x2 => x1 ≥ x2) f → ∀ {s : S
et α}, IsUpperSet s → IsUpperSet (f '' s)
参数：fun x1 x2 => x1 ≥ x2；fun x1 x2 => x1 ≥ x2；f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.Fibration.isLowerSet_image`：∀ {α : Type u_1} {β : Type u_2} {f 
: α → β} [inst : LE α] [inst_1 : LE β],   Relation.Fibration (fun x1 x2 => x1 ≤ 
x2) (fun x1 x2 => x1 ≤ x2…
-/
lemma Fibration.isUpperSet_image [LE α] [LE β] (hf : Fibration (· ≥ ·) (· ≥ ·) f)
    {s : Set α} (hs : IsUpperSet s) : IsUpperSet (f '' s) :=
  @Fibration.isLowerSet_image αᵒᵈ βᵒᵈ _ _ _ hf s hs

alias _root_.IsUpperSet.image_fibration := Fibration.isUpperSet_image
/-
**Relation.fibration_iff_isUpperSet_image_Ici** 是 Mathlib 中的一个引理，位于命名空间 `Relatio
n`。
形式化陈述：fibration_iff_isUpperSet_image_Ici [Preorder α] [LE β] : Fibration (· >= ·
) (· >= ·) f ↔ forall x, IsUpperSet (f '' Ici x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Relation.fibration_iff_isLowerSet_image_Iic`：fibration_iff_isLowerSet_im
age_Iic [Preorder α] [LE β] : Fibration (· <= ·) (· <= ·) f ↔ forall x, IsLowerS
et (f '' Iic x)
-/
lemma fibration_iff_isUpperSet_image_Ici [Preorder α] [LE β] :
    Fibration (· ≥ ·) (· ≥ ·) f ↔ ∀ x, IsUpperSet (f '' Ici x) :=
  @fibration_iff_isLowerSet_image_Iic αᵒᵈ βᵒᵈ _ _ _
/-
**Relation.fibration_iff_isUpperSet_image** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：fibration_iff_isUpperSet_image [Preorder α] [LE β] : Fibration (· >= ·) (·
 >= ·) f ↔ forall s, IsUpperSet s -> IsUpperSet (f '' s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Relation.fibration_iff_isLowerSet_image`：fibration_iff_isLowerSet_image 
[Preorder α] [LE β] : Fibration (· <= ·) (· <= ·) f ↔ forall s, IsLowerSet s -> 
IsLowerSet (f '' s)
-/
lemma fibration_iff_isUpperSet_image [Preorder α] [LE β] :
    Fibration (· ≥ ·) (· ≥ ·) f ↔ ∀ s, IsUpperSet s → IsUpperSet (f '' s) :=
  @fibration_iff_isLowerSet_image αᵒᵈ βᵒᵈ _ _ _
/-
**Relation.fibration_iff_image_Ici** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：fibration_iff_image_Ici [Preorder α] [Preorder β] (hf : Monotone f) : Fibr
ation (· >= ·) (· >= ·) f ↔ forall x, f '' Ici x = Ici (f x)
参数：hf : Monotone f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Relation.fibration_iff_image_Iic`：fibration_iff_image_Iic [Preorder α] [
Preorder β] (hf : Monotone f) : Fibration (· <= ·) (· <= ·) f ↔ forall x, f '' I
ic x = Iic (f x)
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
-/
lemma fibration_iff_image_Ici [Preorder α] [Preorder β] (hf : Monotone f) :
    Fibration (· ≥ ·) (· ≥ ·) f ↔ ∀ x, f '' Ici x = Ici (f x) :=
  fibration_iff_image_Iic hf.dual

end Relation

