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

variable {α β : Type*} {f : α -> β}

/--
lemma `Fibration.isLowerSet_image` / 引理 `Fibration.isLowerSet_image`

English:
lemma Fibration.isLowerSet_image
  statement: [LE α] [LE β] (hf : Fibration (· <= ·) (· <= ·) f)
  proof: by
  rintro _ y' e ⟨x, hx, rfl⟩; obtain ⟨y, e', rfl⟩ := hf e; exact ⟨_, hs e' hx, rfl⟩

alias _root_.IsLowerSet.image_fibration := Fibration.isLowerSet_image

中文:
引理 纤维化.isLowerSet_image
  结论: [LE α] [LE β] (hf : 纤维化 (· <= ·) (· <= ·) f)
  证明: by
  rintro _ y' e ⟨x, hx, rfl⟩; obtain ⟨y, e', rfl⟩ := hf e; exact ⟨_, hs e' hx, rfl⟩

alias _root_.IsLowerSet.image_fibration := Fibration.isLowerSet_image
-/
lemma Fibration.isLowerSet_image [LE α] [LE β] (hf : Fibration (· <= ·) (· <= ·) f)
    {s : Set α} (hs : IsLowerSet s) : IsLowerSet (f '' s) := by
  rintro _ y' e ⟨x, hx, rfl⟩; obtain ⟨y, e', rfl⟩ := hf e; exact ⟨_, hs e' hx, rfl⟩

alias _root_.IsLowerSet.image_fibration := Fibration.isLowerSet_image

/--
lemma `fibration_iff_isLowerSet_image_Iic` / 引理 `fibration_iff_isLowerSet_image_Iic`

English:
lemma fibration_iff_isLowerSet_image_Iic
  given: [Preorder α] [LE β]
  proof: ⟨fun h x => (isLowerSet_Iic x).image_fibration h, fun H x _ e => H x e ⟨x, le_rfl, rfl⟩⟩

中文:
引理 fibration_iff_isLowerSet_image_Iic
  条件: [预序 α] [LE β]
  证明: ⟨fun h x => (isLowerSet_Iic x).image_fibration h, fun H x _ e => H x e ⟨x, le_rfl, rfl⟩⟩

Depends on / 依赖: image_fibration, isLowerSet_Iic, le_rfl
-/
lemma fibration_iff_isLowerSet_image_Iic [Preorder α] [LE β] :
    Fibration (· <= ·) (· <= ·) f ↔ forall x, IsLowerSet (f '' Iic x) :=
  ⟨fun h x => (isLowerSet_Iic x).image_fibration h, fun H x _ e => H x e ⟨x, le_rfl, rfl⟩⟩

/--
lemma `fibration_iff_isLowerSet_image` / 引理 `fibration_iff_isLowerSet_image`

English:
lemma fibration_iff_isLowerSet_image
  given: [Preorder α] [LE β]
  proof: ⟨Fibration.isLowerSet_image,
    fun H => fibration_iff_isLowerSet_image_Iic.mpr (H _ <| isLowerSet_Iic ·)⟩

中文:
引理 fibration_iff_isLowerSet_image
  条件: [预序 α] [LE β]
  证明: ⟨Fibration.isLowerSet_image,
    fun H => fibration_iff_isLowerSet_image_Iic.mpr (H _ <| isLowerSet_Iic ·)⟩

Depends on / 依赖: Fibration, Fibration.isLowerSet_image, fibration_iff_isLowerSet_image_Iic, fibration_iff_isLowerSet_image_Iic.mpr, isLowerSet_Iic, isLowerSet_image
-/
lemma fibration_iff_isLowerSet_image [Preorder α] [LE β] :
    Fibration (· <= ·) (· <= ·) f ↔ forall s, IsLowerSet s -> IsLowerSet (f '' s) :=
  ⟨Fibration.isLowerSet_image,
    fun H => fibration_iff_isLowerSet_image_Iic.mpr (H _ <| isLowerSet_Iic ·)⟩

/--
lemma `fibration_iff_image_Iic` / 引理 `fibration_iff_image_Iic`

English:
lemma fibration_iff_image_Iic
  given: [Preorder α] [Preorder β] (hf : Monotone f)
  proof: ⟨fun H x => le_antisymm (fun _ ⟨_, hy, e⟩ => e ▸ hf hy)
    ((H.isLowerSet_image (isLowerSet_Iic x)).Iic_subset ⟨x, le_rfl, rfl⟩),
    fun H => fibration_iff_isLowerSet_image_Iic.mpr (fun x => (H x).symm ▸ isLowerSet_Iic (f x))⟩

中文:
引理 fibration_iff_image_Iic
  条件: [预序 α] [预序 β] (hf : 递增 f)
  证明: ⟨fun H x => le_antisymm (fun _ ⟨_, hy, e⟩ => e ▸ hf hy)
    ((H.isLowerSet_image (isLowerSet_Iic x)).Iic_subset ⟨x, le_rfl, rfl⟩),
    fun H => fibration_iff_isLowerSet_image_Iic.mpr (fun x => (H x).symm ▸ isLowerSet_Iic (f x))⟩

Depends on / 依赖: H.isLowerSet_image, Iic_subset, fibration_iff_isLowerSet_image_Iic, fibration_iff_isLowerSet_image_Iic.mpr, isLowerSet_Iic, isLowerSet_image, le_antisymm, le_rfl
-/
lemma fibration_iff_image_Iic [Preorder α] [Preorder β] (hf : Monotone f) :
    Fibration (· <= ·) (· <= ·) f ↔ forall x, f '' Iic x = Iic (f x) :=
  ⟨fun H x => le_antisymm (fun _ ⟨_, hy, e⟩ => e ▸ hf hy)
    ((H.isLowerSet_image (isLowerSet_Iic x)).Iic_subset ⟨x, le_rfl, rfl⟩),
    fun H => fibration_iff_isLowerSet_image_Iic.mpr (fun x => (H x).symm ▸ isLowerSet_Iic (f x))⟩

/--
lemma `Fibration.isUpperSet_image` / 引理 `Fibration.isUpperSet_image`

English:
lemma Fibration.isUpperSet_image
  statement: [LE α] [LE β] (hf : Fibration (· >= ·) (· >= ·) f)
  proof: @Fibration.isLowerSet_image αᵒᵈ βᵒᵈ _ _ _ hf s hs

alias _root_.IsUpperSet.image_fibration := Fibration.isUpperSet_image

中文:
引理 纤维化.isUpperSet_image
  结论: [LE α] [LE β] (hf : 纤维化 (· >= ·) (· >= ·) f)
  证明: @Fibration.isLowerSet_image αᵒᵈ βᵒᵈ _ _ _ hf s hs

alias _root_.IsUpperSet.image_fibration := Fibration.isUpperSet_image

Depends on / 依赖: Fibration, Fibration.isLowerSet_image, isLowerSet_image
-/
lemma Fibration.isUpperSet_image [LE α] [LE β] (hf : Fibration (· >= ·) (· >= ·) f)
    {s : Set α} (hs : IsUpperSet s) : IsUpperSet (f '' s) :=
  @Fibration.isLowerSet_image αᵒᵈ βᵒᵈ _ _ _ hf s hs

alias _root_.IsUpperSet.image_fibration := Fibration.isUpperSet_image

/--
lemma `fibration_iff_isUpperSet_image_Ici` / 引理 `fibration_iff_isUpperSet_image_Ici`

English:
lemma fibration_iff_isUpperSet_image_Ici
  given: [Preorder α] [LE β]
  proof: @fibration_iff_isLowerSet_image_Iic αᵒᵈ βᵒᵈ _ _ _

中文:
引理 fibration_iff_isUpperSet_image_Ici
  条件: [预序 α] [LE β]
  证明: @fibration_iff_isLowerSet_image_Iic αᵒᵈ βᵒᵈ _ _ _

Depends on / 依赖: fibration_iff_isLowerSet_image_Iic
-/
lemma fibration_iff_isUpperSet_image_Ici [Preorder α] [LE β] :
    Fibration (· >= ·) (· >= ·) f ↔ forall x, IsUpperSet (f '' Ici x) :=
  @fibration_iff_isLowerSet_image_Iic αᵒᵈ βᵒᵈ _ _ _

/--
lemma `fibration_iff_isUpperSet_image` / 引理 `fibration_iff_isUpperSet_image`

English:
lemma fibration_iff_isUpperSet_image
  given: [Preorder α] [LE β]
  proof: @fibration_iff_isLowerSet_image αᵒᵈ βᵒᵈ _ _ _

中文:
引理 fibration_iff_isUpperSet_image
  条件: [预序 α] [LE β]
  证明: @fibration_iff_isLowerSet_image αᵒᵈ βᵒᵈ _ _ _

Depends on / 依赖: fibration_iff_isLowerSet_image
-/
lemma fibration_iff_isUpperSet_image [Preorder α] [LE β] :
    Fibration (· >= ·) (· >= ·) f ↔ forall s, IsUpperSet s -> IsUpperSet (f '' s) :=
  @fibration_iff_isLowerSet_image αᵒᵈ βᵒᵈ _ _ _

/--
lemma `fibration_iff_image_Ici` / 引理 `fibration_iff_image_Ici`

English:
lemma fibration_iff_image_Ici
  given: [Preorder α] [Preorder β] (hf : Monotone f)
  proof: fibration_iff_image_Iic hf.dual

中文:
引理 fibration_iff_image_Ici
  条件: [预序 α] [预序 β] (hf : 递增 f)
  证明: fibration_iff_image_Iic hf.dual

Depends on / 依赖: fibration_iff_image_Iic, hf.dual
-/
lemma fibration_iff_image_Ici [Preorder α] [Preorder β] (hf : Monotone f) :
    Fibration (· >= ·) (· >= ·) f ↔ forall x, f '' Ici x = Ici (f x) :=
  fibration_iff_image_Iic hf.dual

end Relation
