/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Pullbacks and pushouts in a monoidal category

For numerous simp lemmas of the form `f ≫ g = h`, we add accompanying simp lemmas of the form
`Q ◁ f ≫ Q ◁ g = Q ◁ h` and `f ▷ Q ≫ g ▷ Q = h ▷ Q`. This file and
`Mathlib.CategoryTheory.Monoidal.Limits.HasLimits` are needed to define a monoidal category
structure in `Mathlib.CategoryTheory.Monoidal.Arrow`.

## TODO
An attribute should be developed to automatically generate lemmas of this form.
-/

public section

universe v u

namespace CategoryTheory.MonoidalCategory

open Limits MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace IsPushout

variable {Z X Y P W : C} {f : Z ⟶ X} {g : Z ⟶ Y}
    {inl : X ⟶ P} {inr : Y ⟶ P} (hP : IsPushout f g inl inr)
    {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k)

@[reassoc (attr := simp)]
/--
lemma `whiskerLeft_inl_desc` / 引理 `whiskerLeft_inl_desc`

English:
lemma whiskerLeft_inl_desc
  given: {Q : C}
  proof: by
  rw [← MonoidalCategory.whiskerLeft_comp]; rw [IsPushout.inl_desc]

@[reassoc (attr := simp)]

中文:
引理 whiskerLeft_inl_desc
  条件: {Q : C}
  证明: by
  rw [← MonoidalCategory.whiskerLeft_comp]; rw [IsPushout.inl_desc]

@[reassoc (attr := simp)]

Depends on / 依赖: IsPushout, IsPushout.inl_desc, MonoidalCategory, MonoidalCategory.whiskerLeft_comp, inl_desc, whiskerLeft_comp
-/
lemma whiskerLeft_inl_desc {Q : C} :
    Q ◁ inl ≫ Q ◁ hP.desc h k w = Q ◁ h := by
  rw [← MonoidalCategory.whiskerLeft_comp]; rw [IsPushout.inl_desc]

@[reassoc (attr := simp)]
/--
lemma `whiskerLeft_inr_desc` / 引理 `whiskerLeft_inr_desc`

English:
lemma whiskerLeft_inr_desc
  given: {Q : C}
  proof: by
  rw [← MonoidalCategory.whiskerLeft_comp]; rw [IsPushout.inr_desc]

@[reassoc (attr := simp)]

中文:
引理 whiskerLeft_inr_desc
  条件: {Q : C}
  证明: by
  rw [← MonoidalCategory.whiskerLeft_comp]; rw [IsPushout.inr_desc]

@[reassoc (attr := simp)]

Depends on / 依赖: IsPushout, IsPushout.inr_desc, MonoidalCategory, MonoidalCategory.whiskerLeft_comp, inr_desc, whiskerLeft_comp
-/
lemma whiskerLeft_inr_desc {Q : C} :
    Q ◁ inr ≫ Q ◁ hP.desc h k w = Q ◁ k := by
  rw [← MonoidalCategory.whiskerLeft_comp]; rw [IsPushout.inr_desc]

@[reassoc (attr := simp)]
/--
lemma `inl_desc_whiskerRight` / 引理 `inl_desc_whiskerRight`

English:
lemma inl_desc_whiskerRight
  given: {Q : C}
  proof: by
  rw [← comp_whiskerRight]; rw [IsPushout.inl_desc]

@[reassoc (attr := simp)]

中文:
引理 inl_desc_whiskerRight
  条件: {Q : C}
  证明: by
  rw [← comp_whiskerRight]; rw [IsPushout.inl_desc]

@[reassoc (attr := simp)]

Depends on / 依赖: IsPushout, IsPushout.inl_desc, comp_whiskerRight, inl_desc
-/
lemma inl_desc_whiskerRight {Q : C} :
    inl ▷ Q ≫ hP.desc h k w ▷ Q = h ▷ Q := by
  rw [← comp_whiskerRight]; rw [IsPushout.inl_desc]

@[reassoc (attr := simp)]
/--
lemma `inr_desc_whiskerRight` / 引理 `inr_desc_whiskerRight`

English:
lemma inr_desc_whiskerRight
  given: {Q : C}
  proof: by
  rw [← comp_whiskerRight]; rw [IsPushout.inr_desc]

@[reassoc]

中文:
引理 inr_desc_whiskerRight
  条件: {Q : C}
  证明: by
  rw [← comp_whiskerRight]; rw [IsPushout.inr_desc]

@[reassoc]

Depends on / 依赖: IsPushout, IsPushout.inr_desc, comp_whiskerRight, inr_desc
-/
lemma inr_desc_whiskerRight {Q : C} :
    inr ▷ Q ≫ hP.desc h k w ▷ Q = k ▷ Q := by
  rw [← comp_whiskerRight]; rw [IsPushout.inr_desc]

@[reassoc]
/--
lemma `whiskerLeft_w` / 引理 `whiskerLeft_w`

English:
lemma whiskerLeft_w
  given: (hP : IsPushout f g inl inr) {Q : C}
  proof: by
  simp [← MonoidalCategory.whiskerLeft_comp, hP.w]

@[reassoc]

中文:
引理 whiskerLeft_w
  条件: (hP : IsPushout f g inl inr) {Q : C}
  证明: by
  simp [← MonoidalCategory.whiskerLeft_comp, hP.w]

@[reassoc]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.whiskerLeft_comp, hP.w, whiskerLeft_comp
-/
lemma whiskerLeft_w (hP : IsPushout f g inl inr) {Q : C} :
    Q ◁ f ≫ Q ◁ inl = Q ◁ g ≫ Q ◁ inr := by
  simp [← MonoidalCategory.whiskerLeft_comp, hP.w]

@[reassoc]
/--
lemma `w_whiskerRight` / 引理 `w_whiskerRight`

English:
lemma w_whiskerRight
  given: (hP : IsPushout f g inl inr) {Q : C}
  proof: by
  simp [← MonoidalCategory.comp_whiskerRight, hP.w]

@[reassoc (attr := simp)]

中文:
引理 w_whiskerRight
  条件: (hP : IsPushout f g inl inr) {Q : C}
  证明: by
  simp [← MonoidalCategory.comp_whiskerRight, hP.w]

@[reassoc (attr := simp)]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.comp_whiskerRight, comp_whiskerRight, hP.w
-/
lemma w_whiskerRight (hP : IsPushout f g inl inr) {Q : C} :
    f ▷ Q ≫ inl ▷ Q = g ▷ Q ≫ inr ▷ Q := by
  simp [← MonoidalCategory.comp_whiskerRight, hP.w]

@[reassoc (attr := simp)]
/--
lemma `whiskerLeft_inl_isoPushout_inv` / 引理 `whiskerLeft_inl_isoPushout_inv`

English:
lemma whiskerLeft_inl_isoPushout_inv
  given: [HasPushout f g] {Q : C}
  proof: by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]

中文:
引理 whiskerLeft_inl_isoPushout_inv
  条件: [HasPushout f g] {Q : C}
  证明: by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.whiskerLeft_comp, whiskerLeft_comp
-/
lemma whiskerLeft_inl_isoPushout_inv [HasPushout f g] {Q : C} :
    Q ◁ pushout.inl _ _ ≫ Q ◁ hP.isoPushout.inv = Q ◁ inl := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
/--
lemma `whiskerLeft_inr_isoPushout_inv` / 引理 `whiskerLeft_inr_isoPushout_inv`

English:
lemma whiskerLeft_inr_isoPushout_inv
  given: [HasPushout f g] {Q : C}
  proof: by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]

中文:
引理 whiskerLeft_inr_isoPushout_inv
  条件: [HasPushout f g] {Q : C}
  证明: by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.whiskerLeft_comp, whiskerLeft_comp
-/
lemma whiskerLeft_inr_isoPushout_inv [HasPushout f g] {Q : C} :
    Q ◁ pushout.inr _ _ ≫ Q ◁ hP.isoPushout.inv = Q ◁ inr := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
/--
lemma `whiskerLeft_inl_isoPushout_hom` / 引理 `whiskerLeft_inl_isoPushout_hom`

English:
lemma whiskerLeft_inl_isoPushout_hom
  given: [HasPushout f g] {Q : C}
  proof: by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]

中文:
引理 whiskerLeft_inl_isoPushout_hom
  条件: [HasPushout f g] {Q : C}
  证明: by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.whiskerLeft_comp, whiskerLeft_comp
-/
lemma whiskerLeft_inl_isoPushout_hom [HasPushout f g] {Q : C} :
    Q ◁ inl ≫ Q ◁ hP.isoPushout.hom = Q ◁ pushout.inl _ _ := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
/--
lemma `whiskerLeft_inr_isoPushout_hom` / 引理 `whiskerLeft_inr_isoPushout_hom`

English:
lemma whiskerLeft_inr_isoPushout_hom
  given: [HasPushout f g] {Q : C}
  proof: by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]

中文:
引理 whiskerLeft_inr_isoPushout_hom
  条件: [HasPushout f g] {Q : C}
  证明: by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.whiskerLeft_comp, whiskerLeft_comp
-/
lemma whiskerLeft_inr_isoPushout_hom [HasPushout f g] {Q : C} :
    Q ◁ inr ≫ Q ◁ hP.isoPushout.hom = Q ◁ pushout.inr _ _ := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
/--
lemma `inl_isoPushout_inv_whiskerRight` / 引理 `inl_isoPushout_inv_whiskerRight`

English:
lemma inl_isoPushout_inv_whiskerRight
  given: [HasPushout f g] {Q : C}
  proof: by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]

中文:
引理 inl_isoPushout_inv_whiskerRight
  条件: [HasPushout f g] {Q : C}
  证明: by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]

Depends on / 依赖: comp_whiskerRight
-/
lemma inl_isoPushout_inv_whiskerRight [HasPushout f g] {Q : C} :
    pushout.inl _ _ ▷ Q ≫ hP.isoPushout.inv ▷ Q = inl ▷ Q := by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]
/--
lemma `inr_isoPushout_inv_whiskerRight` / 引理 `inr_isoPushout_inv_whiskerRight`

English:
lemma inr_isoPushout_inv_whiskerRight
  given: [HasPushout f g] {Q : C}
  proof: by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]

中文:
引理 inr_isoPushout_inv_whiskerRight
  条件: [HasPushout f g] {Q : C}
  证明: by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]

Depends on / 依赖: comp_whiskerRight
-/
lemma inr_isoPushout_inv_whiskerRight [HasPushout f g] {Q : C} :
    pushout.inr _ _ ▷ Q ≫ hP.isoPushout.inv ▷ Q = inr ▷ Q := by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]
/--
lemma `inl_isoPushout_hom_whiskerRight` / 引理 `inl_isoPushout_hom_whiskerRight`

English:
lemma inl_isoPushout_hom_whiskerRight
  given: [HasPushout f g] {Q : C}
  proof: by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]

中文:
引理 inl_isoPushout_hom_whiskerRight
  条件: [HasPushout f g] {Q : C}
  证明: by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]

Depends on / 依赖: comp_whiskerRight
-/
lemma inl_isoPushout_hom_whiskerRight [HasPushout f g] {Q : C} :
    inl ▷ Q ≫ hP.isoPushout.hom ▷ Q = pushout.inl _ _ ▷ Q := by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]
/--
lemma `inr_isoPushout_hom_whiskerRight` / 引理 `inr_isoPushout_hom_whiskerRight`

English:
lemma inr_isoPushout_hom_whiskerRight
  given: [HasPushout f g] {Q : C}
  proof: by
  simp [← comp_whiskerRight]

中文:
引理 inr_isoPushout_hom_whiskerRight
  条件: [HasPushout f g] {Q : C}
  证明: by
  simp [← comp_whiskerRight]

Depends on / 依赖: comp_whiskerRight
-/
lemma inr_isoPushout_hom_whiskerRight [HasPushout f g] {Q : C} :
    inr ▷ Q ≫ hP.isoPushout.hom ▷ Q = pushout.inr _ _ ▷ Q := by
  simp [← comp_whiskerRight]

end IsPushout

section Pushout

variable [HasPushouts C]
  {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
  (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k) {Q : C}

@[reassoc]
/--
lemma `Limits.pushout.whiskerLeft_condition` / 引理 `Limits.pushout.whiskerLeft_condition`

English:
lemma Limits.pushout.whiskerLeft_condition
  proof: by
  simp [← MonoidalCategory.whiskerLeft_comp, pushout.condition]

@[reassoc]

中文:
引理 Limits.pushout.whiskerLeft_condition
  证明: by
  simp [← MonoidalCategory.whiskerLeft_comp, pushout.condition]

@[reassoc]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.whiskerLeft_comp, condition, pushout, pushout.condition, whiskerLeft_comp
-/
lemma Limits.pushout.whiskerLeft_condition :
    Q ◁ f ≫ Q ◁ pushout.inl f g = Q ◁ g ≫ Q ◁ pushout.inr f g := by
  simp [← MonoidalCategory.whiskerLeft_comp, pushout.condition]

@[reassoc]
/--
lemma `Limits.pushout.condition_whiskerRight` / 引理 `Limits.pushout.condition_whiskerRight`

English:
lemma Limits.pushout.condition_whiskerRight
  proof: by
  simp [← comp_whiskerRight, pushout.condition]

中文:
引理 Limits.pushout.condition_whiskerRight
  证明: by
  simp [← comp_whiskerRight, pushout.condition]

Depends on / 依赖: comp_whiskerRight, condition, pushout, pushout.condition
-/
lemma Limits.pushout.condition_whiskerRight :
    f ▷ Q ≫ pushout.inl f g ▷ Q = g ▷ Q ≫ pushout.inr f g ▷ Q := by
  simp [← comp_whiskerRight, pushout.condition]

variable {A B X Y Z W : C} {f : A ⟶ B} {g : X ⟶ Y}

@[reassoc]
/--
lemma `Limits.pushout.associator_naturality_left_condition` / 引理 `Limits.pushout.associator_naturality_left_condition`

English:
lemma Limits.pushout.associator_naturality_left_condition
  given: {h : Z otimes W ⟶ X}
  proof: by
  rw [associator_naturality_left_assoc]; rw [← whisker_exchange_assoc]; rw [pushout.condition]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]

@[reassoc]

中文:
引理 Limits.pushout.associator_naturality_left_condition
  条件: {h : Z otimes W ⟶ X}
  证明: by
  rw [associator_naturality_left_assoc]; rw [← whisker_exchange_assoc]; rw [pushout.condition]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]

@[reassoc]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.whiskerLeft_comp_assoc, associator_naturality_left_assoc, condition, pushout, pushout.condition, whiskerLeft_comp_assoc, whisker_exchange_assoc
-/
lemma Limits.pushout.associator_naturality_left_condition {h : Z otimes W ⟶ X} :
    f ▷ Z ▷ W ≫ (α_ B Z W).hom ≫ B ◁ h ≫ pushout.inl (f ▷ X) (A ◁ g) =
      (α_ A Z W).hom ≫ A ◁ (h ≫ g) ≫ pushout.inr (f ▷ X) (A ◁ g) := by
  rw [associator_naturality_left_assoc]; rw [← whisker_exchange_assoc]; rw [pushout.condition]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]

@[reassoc]
/--
lemma `Limits.pushout.associator_inv_naturality_right_condition` / 引理 `Limits.pushout.associator_inv_naturality_right_condition`

English:
lemma Limits.pushout.associator_inv_naturality_right_condition
  given: {h : Z otimes W ⟶ A}
  proof: by
  rw [associator_inv_naturality_right_assoc]; rw [whisker_exchange_assoc]; rw [← pushout.condition]; rw [← comp_whiskerRight_assoc]

@[reassoc (attr := simp)]

中文:
引理 Limits.pushout.associator_inv_naturality_right_condition
  条件: {h : Z otimes W ⟶ A}
  证明: by
  rw [associator_inv_naturality_right_assoc]; rw [whisker_exchange_assoc]; rw [← pushout.condition]; rw [← comp_whiskerRight_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: associator_inv_naturality_right_assoc, comp_whiskerRight_assoc, condition, pushout, pushout.condition, whisker_exchange_assoc
-/
lemma Limits.pushout.associator_inv_naturality_right_condition {h : Z otimes W ⟶ A} :
    Z ◁ W ◁ g ≫ (α_ Z W Y).inv ≫ h ▷ Y ≫ pushout.inr (f ▷ X) (A ◁ g) =
      (α_ Z W X).inv ≫ (h ≫ f) ▷ X ≫ pushout.inl (f ▷ X) (A ◁ g) := by
  rw [associator_inv_naturality_right_assoc]; rw [whisker_exchange_assoc]; rw [← pushout.condition]; rw [← comp_whiskerRight_assoc]

@[reassoc (attr := simp)]
/--
lemma `Limits.whiskerLeft_inl_comp_pushoutSymmetry_hom` / 引理 `Limits.whiskerLeft_inl_comp_pushoutSymmetry_hom`

English:
lemma Limits.whiskerLeft_inl_comp_pushoutSymmetry_hom
  given: (f : X ⟶ Y) (g : X ⟶ Z)
  proof: by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]

中文:
引理 Limits.whiskerLeft_inl_comp_pushoutSymmetry_hom
  条件: (f : X ⟶ Y) (g : X ⟶ Z)
  证明: by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.whiskerLeft_comp, whiskerLeft_comp
-/
lemma Limits.whiskerLeft_inl_comp_pushoutSymmetry_hom (f : X ⟶ Y) (g : X ⟶ Z) :
    Q ◁ pushout.inl f g ≫ Q ◁ (pushoutSymmetry f g).hom = Q ◁ pushout.inr g f := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
/--
lemma `Limits.whiskerLeft_inr_comp_pushoutSymmetry_hom` / 引理 `Limits.whiskerLeft_inr_comp_pushoutSymmetry_hom`

English:
lemma Limits.whiskerLeft_inr_comp_pushoutSymmetry_hom
  given: (f : X ⟶ Y) (g : X ⟶ Z)
  proof: by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]

中文:
引理 Limits.whiskerLeft_inr_comp_pushoutSymmetry_hom
  条件: (f : X ⟶ Y) (g : X ⟶ Z)
  证明: by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.whiskerLeft_comp, whiskerLeft_comp
-/
lemma Limits.whiskerLeft_inr_comp_pushoutSymmetry_hom (f : X ⟶ Y) (g : X ⟶ Z) :
    Q ◁ pushout.inr f g ≫ Q ◁ (pushoutSymmetry f g).hom = Q ◁ pushout.inl g f := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
/--
lemma `Limits.inl_comp_pushoutSymmetry_hom_whiskerRight` / 引理 `Limits.inl_comp_pushoutSymmetry_hom_whiskerRight`

English:
lemma Limits.inl_comp_pushoutSymmetry_hom_whiskerRight
  given: (f : X ⟶ Y) (g : X ⟶ Z)
  proof: by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]

中文:
引理 Limits.inl_comp_pushoutSymmetry_hom_whiskerRight
  条件: (f : X ⟶ Y) (g : X ⟶ Z)
  证明: by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]

Depends on / 依赖: comp_whiskerRight
-/
lemma Limits.inl_comp_pushoutSymmetry_hom_whiskerRight (f : X ⟶ Y) (g : X ⟶ Z) :
    pushout.inl f g ▷ Q ≫ (pushoutSymmetry f g).hom ▷ Q = pushout.inr g f ▷ Q := by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]
/--
lemma `Limits.inr_comp_pushoutSymmetry_hom_whiskerRight` / 引理 `Limits.inr_comp_pushoutSymmetry_hom_whiskerRight`

English:
lemma Limits.inr_comp_pushoutSymmetry_hom_whiskerRight
  given: (f : X ⟶ Y) (g : X ⟶ Z)
  proof: by
  simp [← comp_whiskerRight]

中文:
引理 Limits.inr_comp_pushoutSymmetry_hom_whiskerRight
  条件: (f : X ⟶ Y) (g : X ⟶ Z)
  证明: by
  simp [← comp_whiskerRight]

Depends on / 依赖: comp_whiskerRight
-/
lemma Limits.inr_comp_pushoutSymmetry_hom_whiskerRight (f : X ⟶ Y) (g : X ⟶ Z) :
    pushout.inr f g ▷ Q ≫ (pushoutSymmetry f g).hom ▷ Q = pushout.inl g f ▷ Q := by
  simp [← comp_whiskerRight]

end Pushout

end CategoryTheory.MonoidalCategory
