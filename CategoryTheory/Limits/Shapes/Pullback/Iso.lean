/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# The pullback of an isomorphism

This file provides some basic results about the pullback (and pushout) of an isomorphism.

-/

@[expose] public section

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {X Y Z : C}

section PullbackLeftIso

open WalkingCospan

variable (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso f]

/--
Definition of `pullbackConeOfLeftIso` / `pullbackConeOfLeftIso` 的定义

English:
definition pullbackConeOfLeftIso
  signature: : PullbackCone f g
  body: PullbackCone.mk (g ≫ inv f) (𝟙 _) by simp

@[simp]

中文:
定义 pullbackConeOfLeftIso
  签名: : PullbackCone f g
  定义体: PullbackCone.mk (g ≫ inv f) (𝟙 _) by simp

@[simp]

Depends on / 依赖: PullbackCone, PullbackCone.mk
-/
def pullbackConeOfLeftIso : PullbackCone f g :=
PullbackCone.mk (g ≫ inv f) (𝟙 _) by simp

@[simp]
/--
theorem `pullbackConeOfLeftIso_x` / 定理 `pullbackConeOfLeftIso_x`

English:
theorem pullbackConeOfLeftIso_x
  statement: (pullbackConeOfLeftIso f g).pt = Y
  proof: rfl

@[simp]

中文:
定理 pullbackConeOfLeftIso_x
  结论: (pullbackConeOfLeftIso f g).pt = Y
  证明: rfl

@[simp]
-/
theorem pullbackConeOfLeftIso_x : (pullbackConeOfLeftIso f g).pt = Y := rfl

@[simp]
/--
theorem `pullbackConeOfLeftIso_fst` / 定理 `pullbackConeOfLeftIso_fst`

English:
theorem pullbackConeOfLeftIso_fst
  statement: (pullbackConeOfLeftIso f g).fst = g ≫ inv f
  proof: rfl

@[simp]

中文:
定理 pullbackConeOfLeftIso_fst
  结论: (pullbackConeOfLeftIso f g).fst = g ≫ inv f
  证明: rfl

@[simp]
-/
theorem pullbackConeOfLeftIso_fst : (pullbackConeOfLeftIso f g).fst = g ≫ inv f := rfl

@[simp]
/--
theorem `pullbackConeOfLeftIso_snd` / 定理 `pullbackConeOfLeftIso_snd`

English:
theorem pullbackConeOfLeftIso_snd
  statement: (pullbackConeOfLeftIso f g).snd = 𝟙 _
  proof: rfl

中文:
定理 pullbackConeOfLeftIso_snd
  结论: (pullbackConeOfLeftIso f g).snd = 𝟙 _
  证明: rfl
-/
theorem pullbackConeOfLeftIso_snd : (pullbackConeOfLeftIso f g).snd = 𝟙 _ := rfl

/--
theorem `pullbackConeOfLeftIso_π_app_none` / 定理 `pullbackConeOfLeftIso_π_app_none`

English:
theorem pullbackConeOfLeftIso_π_app_none
  statement: (pullbackConeOfLeftIso f g).π.app none = g
  proof: by simp

中文:
定理 pullbackConeOfLeftIso_π_app_none
  结论: (pullbackConeOfLeftIso f g).π.app none = g
  证明: by simp
-/
theorem pullbackConeOfLeftIso_π_app_none : (pullbackConeOfLeftIso f g).π.app none = g := by simp

/--
theorem `pullbackConeOfLeftIso_π_app_left` / 定理 `pullbackConeOfLeftIso_π_app_left`

English:
theorem pullbackConeOfLeftIso_π_app_left
  statement: (pullbackConeOfLeftIso f g).π.app left = g ≫ inv f
  proof: rfl

中文:
定理 pullbackConeOfLeftIso_π_app_left
  结论: (pullbackConeOfLeftIso f g).π.app left = g ≫ inv f
  证明: rfl
-/
theorem pullbackConeOfLeftIso_π_app_left : (pullbackConeOfLeftIso f g).π.app left = g ≫ inv f :=
  rfl

/--
theorem `pullbackConeOfLeftIso_π_app_right` / 定理 `pullbackConeOfLeftIso_π_app_right`

English:
theorem pullbackConeOfLeftIso_π_app_right
  statement: (pullbackConeOfLeftIso f g).π.app right = 𝟙 _
  proof: rfl

中文:
定理 pullbackConeOfLeftIso_π_app_right
  结论: (pullbackConeOfLeftIso f g).π.app right = 𝟙 _
  证明: rfl
-/
theorem pullbackConeOfLeftIso_π_app_right : (pullbackConeOfLeftIso f g).π.app right = 𝟙 _ := rfl

/--
Definition of `pullbackConeOfLeftIsoIsLimit` / `pullbackConeOfLeftIsoIsLimit` 的定义

English:
definition pullbackConeOfLeftIsoIsLimit
  signature: : IsLimit (pullbackConeOfLeftIso f g)
  body: PullbackCone.isLimitAux' _ fun s => ⟨s.snd, by simp [← s.condition_assoc]⟩

中文:
定义 pullbackConeOfLeftIsoIsLimit
  签名: : 是极限 (pullbackConeOfLeftIso f g)
  定义体: PullbackCone.isLimitAux' _ fun s => ⟨s.snd, by simp [← s.condition_assoc]⟩

Depends on / 依赖: PullbackCone, PullbackCone.isLimitAux, condition_assoc, isLimitAux, s.condition_assoc, s.snd
-/
def pullbackConeOfLeftIsoIsLimit : IsLimit (pullbackConeOfLeftIso f g) :=
  PullbackCone.isLimitAux' _ fun s => ⟨s.snd, by simp [← s.condition_assoc]⟩

/--
theorem `hasPullback_of_left_iso` / 定理 `hasPullback_of_left_iso`

English:
theorem hasPullback_of_left_iso
  statement: HasPullback f g
  proof: ⟨⟨⟨_, pullbackConeOfLeftIsoIsLimit f g⟩⟩⟩

中文:
定理 hasPullback_of_left_iso
  结论: HasPullback f g
  证明: ⟨⟨⟨_, pullbackConeOfLeftIsoIsLimit f g⟩⟩⟩

Depends on / 依赖: pullbackConeOfLeftIsoIsLimit
-/
theorem hasPullback_of_left_iso : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsoIsLimit f g⟩⟩⟩

attribute [local instance] hasPullback_of_left_iso

set_option backward.isDefEq.respectTransparency false in
/--
Instance `pullback_snd_iso_of_left_iso` / 实例 `pullback_snd_iso_of_left_iso`

English:
instance pullback_snd_iso_of_left_iso
  signature: : IsIso (pullback.snd f g)
  body: by
  refine ⟨⟨pullback.lift (g ≫ inv f) (𝟙 _) (by simp), ?_, by simp⟩⟩
  ext
  · simp [← pullback.condition_assoc]
  · simp

@[reassoc (attr := simp)]

中文:
实例 pullback_snd_iso_of_left_iso
  签名: : 是同构 (pullback.snd f g)
  定义体: by
  refine ⟨⟨pullback.lift (g ≫ inv f) (𝟙 _) (by simp), ?_, by simp⟩⟩
  ext
  · simp [← pullback.condition_assoc]
  · simp

@[reassoc (attr := simp)]

Depends on / 依赖: condition_assoc, pullback, pullback.condition_assoc, pullback.lift
-/
instance pullback_snd_iso_of_left_iso : IsIso (pullback.snd f g) := by
  refine ⟨⟨pullback.lift (g ≫ inv f) (𝟙 _) (by simp), ?_, by simp⟩⟩
  ext
  · simp [← pullback.condition_assoc]
  · simp

@[reassoc (attr := simp)]
/--
lemma `pullback_inv_snd_fst_of_left_isIso` / 引理 `pullback_inv_snd_fst_of_left_isIso`

English:
lemma pullback_inv_snd_fst_of_left_isIso
  proof: by
  rw [IsIso.inv_comp_eq]; rw [← pullback.condition_assoc]; rw [IsIso.hom_inv_id]; rw [Category.comp_id]

中文:
引理 pullback_inv_snd_fst_of_left_isIso
  证明: by
  rw [IsIso.inv_comp_eq]; rw [← pullback.condition_assoc]; rw [IsIso.hom_inv_id]; rw [Category.comp_id]

Depends on / 依赖: Category, Category.comp_id, IsIso.hom_inv_id, IsIso.inv_comp_eq, comp_id, condition_assoc, hom_inv_id, inv_comp_eq, pullback, pullback.condition_assoc
-/
lemma pullback_inv_snd_fst_of_left_isIso :
    inv (pullback.snd f g) ≫ pullback.fst f g = g ≫ inv f := by
  rw [IsIso.inv_comp_eq]; rw [← pullback.condition_assoc]; rw [IsIso.hom_inv_id]; rw [Category.comp_id]

end PullbackLeftIso

section PullbackRightIso

open WalkingCospan

variable (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso g]

/--
Definition of `pullbackConeOfRightIso` / `pullbackConeOfRightIso` 的定义

English:
definition pullbackConeOfRightIso
  signature: : PullbackCone f g
  body: PullbackCone.mk (𝟙 _) (f ≫ inv g) by simp

@[simp]

中文:
定义 pullbackConeOfRightIso
  签名: : PullbackCone f g
  定义体: PullbackCone.mk (𝟙 _) (f ≫ inv g) by simp

@[simp]

Depends on / 依赖: PullbackCone, PullbackCone.mk
-/
def pullbackConeOfRightIso : PullbackCone f g :=
PullbackCone.mk (𝟙 _) (f ≫ inv g) by simp

@[simp]
/--
theorem `pullbackConeOfRightIso_x` / 定理 `pullbackConeOfRightIso_x`

English:
theorem pullbackConeOfRightIso_x
  statement: (pullbackConeOfRightIso f g).pt = X
  proof: rfl

@[simp]

中文:
定理 pullbackConeOfRightIso_x
  结论: (pullbackConeOfRightIso f g).pt = X
  证明: rfl

@[simp]
-/
theorem pullbackConeOfRightIso_x : (pullbackConeOfRightIso f g).pt = X := rfl

@[simp]
/--
theorem `pullbackConeOfRightIso_fst` / 定理 `pullbackConeOfRightIso_fst`

English:
theorem pullbackConeOfRightIso_fst
  statement: (pullbackConeOfRightIso f g).fst = 𝟙 _
  proof: rfl

@[simp]

中文:
定理 pullbackConeOfRightIso_fst
  结论: (pullbackConeOfRightIso f g).fst = 𝟙 _
  证明: rfl

@[simp]
-/
theorem pullbackConeOfRightIso_fst : (pullbackConeOfRightIso f g).fst = 𝟙 _ := rfl

@[simp]
/--
theorem `pullbackConeOfRightIso_snd` / 定理 `pullbackConeOfRightIso_snd`

English:
theorem pullbackConeOfRightIso_snd
  statement: (pullbackConeOfRightIso f g).snd = f ≫ inv g
  proof: rfl

中文:
定理 pullbackConeOfRightIso_snd
  结论: (pullbackConeOfRightIso f g).snd = f ≫ inv g
  证明: rfl
-/
theorem pullbackConeOfRightIso_snd : (pullbackConeOfRightIso f g).snd = f ≫ inv g := rfl

/--
theorem `pullbackConeOfRightIso_π_app_none` / 定理 `pullbackConeOfRightIso_π_app_none`

English:
theorem pullbackConeOfRightIso_π_app_none
  statement: (pullbackConeOfRightIso f g).π.app none = f
  proof: by simp

中文:
定理 pullbackConeOfRightIso_π_app_none
  结论: (pullbackConeOfRightIso f g).π.app none = f
  证明: by simp
-/
theorem pullbackConeOfRightIso_π_app_none : (pullbackConeOfRightIso f g).π.app none = f := by simp

/--
theorem `pullbackConeOfRightIso_π_app_left` / 定理 `pullbackConeOfRightIso_π_app_left`

English:
theorem pullbackConeOfRightIso_π_app_left
  statement: (pullbackConeOfRightIso f g).π.app left = 𝟙 _
  proof: rfl

中文:
定理 pullbackConeOfRightIso_π_app_left
  结论: (pullbackConeOfRightIso f g).π.app left = 𝟙 _
  证明: rfl
-/
theorem pullbackConeOfRightIso_π_app_left : (pullbackConeOfRightIso f g).π.app left = 𝟙 _ :=
  rfl

/--
theorem `pullbackConeOfRightIso_π_app_right` / 定理 `pullbackConeOfRightIso_π_app_right`

English:
theorem pullbackConeOfRightIso_π_app_right
  statement: (pullbackConeOfRightIso f g).π.app right = f ≫ inv g
  proof: rfl

中文:
定理 pullbackConeOfRightIso_π_app_right
  结论: (pullbackConeOfRightIso f g).π.app right = f ≫ inv g
  证明: rfl
-/
theorem pullbackConeOfRightIso_π_app_right : (pullbackConeOfRightIso f g).π.app right = f ≫ inv g :=
  rfl

/--
Definition of `pullbackConeOfRightIsoIsLimit` / `pullbackConeOfRightIsoIsLimit` 的定义

English:
definition pullbackConeOfRightIsoIsLimit
  signature: : IsLimit (pullbackConeOfRightIso f g)
  body: PullbackCone.isLimitAux' _ fun s => ⟨s.fst, by simp [s.condition_assoc]⟩

中文:
定义 pullbackConeOfRightIsoIsLimit
  签名: : 是极限 (pullbackConeOfRightIso f g)
  定义体: PullbackCone.isLimitAux' _ fun s => ⟨s.fst, by simp [s.condition_assoc]⟩

Depends on / 依赖: PullbackCone, PullbackCone.isLimitAux, condition_assoc, isLimitAux, s.condition_assoc, s.fst
-/
def pullbackConeOfRightIsoIsLimit : IsLimit (pullbackConeOfRightIso f g) :=
  PullbackCone.isLimitAux' _ fun s => ⟨s.fst, by simp [s.condition_assoc]⟩

/--
theorem `hasPullback_of_right_iso` / 定理 `hasPullback_of_right_iso`

English:
theorem hasPullback_of_right_iso
  statement: HasPullback f g
  proof: ⟨⟨⟨_, pullbackConeOfRightIsoIsLimit f g⟩⟩⟩

中文:
定理 hasPullback_of_right_iso
  结论: HasPullback f g
  证明: ⟨⟨⟨_, pullbackConeOfRightIsoIsLimit f g⟩⟩⟩

Depends on / 依赖: pullbackConeOfRightIsoIsLimit
-/
theorem hasPullback_of_right_iso : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfRightIsoIsLimit f g⟩⟩⟩

attribute [local instance] hasPullback_of_right_iso

set_option backward.isDefEq.respectTransparency false in
/--
Instance `pullback_fst_iso_of_right_iso` / 实例 `pullback_fst_iso_of_right_iso`

English:
instance pullback_fst_iso_of_right_iso
  signature: : IsIso (pullback.fst f g)
  body: by
  refine ⟨⟨pullback.lift (𝟙 _) (f ≫ inv g) (by simp), ?_, by simp⟩⟩
  ext
  · simp
  · simp [pullback.condition_assoc]

@[reassoc (attr := simp)]

中文:
实例 pullback_fst_iso_of_right_iso
  签名: : 是同构 (pullback.fst f g)
  定义体: by
  refine ⟨⟨pullback.lift (𝟙 _) (f ≫ inv g) (by simp), ?_, by simp⟩⟩
  ext
  · simp
  · simp [pullback.condition_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: condition_assoc, pullback, pullback.condition_assoc, pullback.lift
-/
instance pullback_fst_iso_of_right_iso : IsIso (pullback.fst f g) := by
  refine ⟨⟨pullback.lift (𝟙 _) (f ≫ inv g) (by simp), ?_, by simp⟩⟩
  ext
  · simp
  · simp [pullback.condition_assoc]

@[reassoc (attr := simp)]
/--
lemma `pullback_inv_fst_snd_of_right_isIso` / 引理 `pullback_inv_fst_snd_of_right_isIso`

English:
lemma pullback_inv_fst_snd_of_right_isIso
  proof: by
  rw [IsIso.inv_comp_eq]; rw [pullback.condition_assoc]; rw [IsIso.hom_inv_id]; rw [Category.comp_id]

中文:
引理 pullback_inv_fst_snd_of_right_isIso
  证明: by
  rw [IsIso.inv_comp_eq]; rw [pullback.condition_assoc]; rw [IsIso.hom_inv_id]; rw [Category.comp_id]

Depends on / 依赖: Category, Category.comp_id, IsIso.hom_inv_id, IsIso.inv_comp_eq, comp_id, condition_assoc, hom_inv_id, inv_comp_eq, pullback, pullback.condition_assoc
-/
lemma pullback_inv_fst_snd_of_right_isIso :
    inv (pullback.fst f g) ≫ pullback.snd f g = f ≫ inv g := by
  rw [IsIso.inv_comp_eq]; rw [pullback.condition_assoc]; rw [IsIso.hom_inv_id]; rw [Category.comp_id]

end PullbackRightIso

section PushoutLeftIso

open WalkingSpan

variable (f : X ⟶ Y) (g : X ⟶ Z) [IsIso f]

/--
Definition of `pushoutCoconeOfLeftIso` / `pushoutCoconeOfLeftIso` 的定义

English:
definition pushoutCoconeOfLeftIso
  signature: : PushoutCocone f g
  body: PushoutCocone.mk (inv f ≫ g) (𝟙 _) by simp

@[simp]

中文:
定义 pushoutCoconeOfLeftIso
  签名: : PushoutCocone f g
  定义体: PushoutCocone.mk (inv f ≫ g) (𝟙 _) by simp

@[simp]

Depends on / 依赖: PushoutCocone, PushoutCocone.mk
-/
def pushoutCoconeOfLeftIso : PushoutCocone f g :=
PushoutCocone.mk (inv f ≫ g) (𝟙 _) by simp

@[simp]
/--
theorem `pushoutCoconeOfLeftIso_x` / 定理 `pushoutCoconeOfLeftIso_x`

English:
theorem pushoutCoconeOfLeftIso_x
  statement: (pushoutCoconeOfLeftIso f g).pt = Z
  proof: rfl

@[simp]

中文:
定理 pushoutCoconeOfLeftIso_x
  结论: (pushoutCoconeOfLeftIso f g).pt = Z
  证明: rfl

@[simp]
-/
theorem pushoutCoconeOfLeftIso_x : (pushoutCoconeOfLeftIso f g).pt = Z := rfl

@[simp]
/--
theorem `pushoutCoconeOfLeftIso_inl` / 定理 `pushoutCoconeOfLeftIso_inl`

English:
theorem pushoutCoconeOfLeftIso_inl
  statement: (pushoutCoconeOfLeftIso f g).inl = inv f ≫ g
  proof: rfl

@[simp]

中文:
定理 pushoutCoconeOfLeftIso_inl
  结论: (pushoutCoconeOfLeftIso f g).inl = inv f ≫ g
  证明: rfl

@[simp]
-/
theorem pushoutCoconeOfLeftIso_inl : (pushoutCoconeOfLeftIso f g).inl = inv f ≫ g := rfl

@[simp]
/--
theorem `pushoutCoconeOfLeftIso_inr` / 定理 `pushoutCoconeOfLeftIso_inr`

English:
theorem pushoutCoconeOfLeftIso_inr
  statement: (pushoutCoconeOfLeftIso f g).inr = 𝟙 _
  proof: rfl

中文:
定理 pushoutCoconeOfLeftIso_inr
  结论: (pushoutCoconeOfLeftIso f g).inr = 𝟙 _
  证明: rfl
-/
theorem pushoutCoconeOfLeftIso_inr : (pushoutCoconeOfLeftIso f g).inr = 𝟙 _ := rfl

/--
theorem `pushoutCoconeOfLeftIso_ι_app_none` / 定理 `pushoutCoconeOfLeftIso_ι_app_none`

English:
theorem pushoutCoconeOfLeftIso_ι_app_none
  statement: (pushoutCoconeOfLeftIso f g).ι.app none = g
  proof: by
  simp

@[simp]

中文:
定理 pushoutCoconeOfLeftIso_ι_app_none
  结论: (pushoutCoconeOfLeftIso f g).ι.app none = g
  证明: by
  simp

@[simp]

Depends on / 依赖: MorphismProperty, MorphismProperty.colimMap, colimMap
-/
theorem pushoutCoconeOfLeftIso_ι_app_none : (pushoutCoconeOfLeftIso f g).ι.app none = g := by
  simp

@[simp]
/--
theorem `pushoutCoconeOfLeftIso_ι_app_left` / 定理 `pushoutCoconeOfLeftIso_ι_app_left`

English:
theorem pushoutCoconeOfLeftIso_ι_app_left
  statement: (pushoutCoconeOfLeftIso f g).ι.app left = inv f ≫ g
  proof: rfl

@[simp]

中文:
定理 pushoutCoconeOfLeftIso_ι_app_left
  结论: (pushoutCoconeOfLeftIso f g).ι.app left = inv f ≫ g
  证明: rfl

@[simp]
-/
theorem pushoutCoconeOfLeftIso_ι_app_left : (pushoutCoconeOfLeftIso f g).ι.app left = inv f ≫ g :=
  rfl

@[simp]
/--
theorem `pushoutCoconeOfLeftIso_ι_app_right` / 定理 `pushoutCoconeOfLeftIso_ι_app_right`

English:
theorem pushoutCoconeOfLeftIso_ι_app_right
  statement: (pushoutCoconeOfLeftIso f g).ι.app right = 𝟙 _
  proof: rfl

中文:
定理 pushoutCoconeOfLeftIso_ι_app_right
  结论: (pushoutCoconeOfLeftIso f g).ι.app right = 𝟙 _
  证明: rfl
-/
theorem pushoutCoconeOfLeftIso_ι_app_right : (pushoutCoconeOfLeftIso f g).ι.app right = 𝟙 _ := rfl

/--
Definition of `pushoutCoconeOfLeftIsoIsLimit` / `pushoutCoconeOfLeftIsoIsLimit` 的定义

English:
definition pushoutCoconeOfLeftIsoIsLimit
  signature: : IsColimit (pushoutCoconeOfLeftIso f g)
  body: PushoutCocone.isColimitAux' _ fun s => ⟨s.inr, by simp [← s.condition]⟩

中文:
定义 pushoutCoconeOfLeftIsoIsLimit
  签名: : 是余极限 (pushoutCoconeOfLeftIso f g)
  定义体: PushoutCocone.isColimitAux' _ fun s => ⟨s.inr, by simp [← s.condition]⟩

Depends on / 依赖: PushoutCocone, PushoutCocone.isColimitAux, condition, isColimitAux, s.condition, s.inr
-/
def pushoutCoconeOfLeftIsoIsLimit : IsColimit (pushoutCoconeOfLeftIso f g) :=
  PushoutCocone.isColimitAux' _ fun s => ⟨s.inr, by simp [← s.condition]⟩

/--
theorem `hasPushout_of_left_iso` / 定理 `hasPushout_of_left_iso`

English:
theorem hasPushout_of_left_iso
  statement: HasPushout f g
  proof: ⟨⟨⟨_, pushoutCoconeOfLeftIsoIsLimit f g⟩⟩⟩

中文:
定理 hasPushout_of_left_iso
  结论: HasPushout f g
  证明: ⟨⟨⟨_, pushoutCoconeOfLeftIsoIsLimit f g⟩⟩⟩

Depends on / 依赖: pushoutCoconeOfLeftIsoIsLimit
-/
theorem hasPushout_of_left_iso : HasPushout f g :=
  ⟨⟨⟨_, pushoutCoconeOfLeftIsoIsLimit f g⟩⟩⟩

attribute [local instance] hasPushout_of_left_iso

set_option backward.isDefEq.respectTransparency false in
/--
Instance `pushout_inr_iso_of_left_iso` / 实例 `pushout_inr_iso_of_left_iso`

English:
instance pushout_inr_iso_of_left_iso
  signature: : IsIso (pushout.inr f g)
  body: by
  refine ⟨⟨pushout.desc (inv f ≫ g) (𝟙 _) (by simp), by simp, ?_⟩⟩
  ext
  · simp [← pushout.condition]
  · simp

@[reassoc (attr := simp)]

中文:
实例 pushout_inr_iso_of_left_iso
  签名: : 是同构 (pushout.inr f g)
  定义体: by
  refine ⟨⟨pushout.desc (inv f ≫ g) (𝟙 _) (by simp), by simp, ?_⟩⟩
  ext
  · simp [← pushout.condition]
  · simp

@[reassoc (attr := simp)]

Depends on / 依赖: condition, pushout, pushout.condition, pushout.desc
-/
instance pushout_inr_iso_of_left_iso : IsIso (pushout.inr f g) := by
  refine ⟨⟨pushout.desc (inv f ≫ g) (𝟙 _) (by simp), by simp, ?_⟩⟩
  ext
  · simp [← pushout.condition]
  · simp

@[reassoc (attr := simp)]
/--
lemma `pushout_inl_inv_inr_of_right_isIso` / 引理 `pushout_inl_inv_inr_of_right_isIso`

English:
lemma pushout_inl_inv_inr_of_right_isIso
  proof: by
  rw [IsIso.eq_inv_comp]; rw [pushout.condition_assoc]; rw [IsIso.hom_inv_id]; rw [Category.comp_id]

中文:
引理 pushout_inl_inv_inr_of_right_isIso
  证明: by
  rw [IsIso.eq_inv_comp]; rw [pushout.condition_assoc]; rw [IsIso.hom_inv_id]; rw [Category.comp_id]

Depends on / 依赖: Category, Category.comp_id, IsIso.eq_inv_comp, IsIso.hom_inv_id, comp_id, condition_assoc, eq_inv_comp, hom_inv_id, pushout, pushout.condition_assoc
-/
lemma pushout_inl_inv_inr_of_right_isIso :
    pushout.inl f g ≫ inv (pushout.inr f g) = inv f ≫ g := by
  rw [IsIso.eq_inv_comp]; rw [pushout.condition_assoc]; rw [IsIso.hom_inv_id]; rw [Category.comp_id]

end PushoutLeftIso

section PushoutRightIso

open WalkingSpan

variable (f : X ⟶ Y) (g : X ⟶ Z) [IsIso g]

/--
Definition of `pushoutCoconeOfRightIso` / `pushoutCoconeOfRightIso` 的定义

English:
definition pushoutCoconeOfRightIso
  signature: : PushoutCocone f g
  body: PushoutCocone.mk (𝟙 _) (inv g ≫ f) by simp

@[simp]

中文:
定义 pushoutCoconeOfRightIso
  签名: : PushoutCocone f g
  定义体: PushoutCocone.mk (𝟙 _) (inv g ≫ f) by simp

@[simp]

Depends on / 依赖: PushoutCocone, PushoutCocone.mk
-/
def pushoutCoconeOfRightIso : PushoutCocone f g :=
PushoutCocone.mk (𝟙 _) (inv g ≫ f) by simp

@[simp]
/--
theorem `pushoutCoconeOfRightIso_x` / 定理 `pushoutCoconeOfRightIso_x`

English:
theorem pushoutCoconeOfRightIso_x
  statement: (pushoutCoconeOfRightIso f g).pt = Y
  proof: rfl

@[simp]

中文:
定理 pushoutCoconeOfRightIso_x
  结论: (pushoutCoconeOfRightIso f g).pt = Y
  证明: rfl

@[simp]
-/
theorem pushoutCoconeOfRightIso_x : (pushoutCoconeOfRightIso f g).pt = Y := rfl

@[simp]
/--
theorem `pushoutCoconeOfRightIso_inl` / 定理 `pushoutCoconeOfRightIso_inl`

English:
theorem pushoutCoconeOfRightIso_inl
  statement: (pushoutCoconeOfRightIso f g).inl = 𝟙 _
  proof: rfl

@[simp]

中文:
定理 pushoutCoconeOfRightIso_inl
  结论: (pushoutCoconeOfRightIso f g).inl = 𝟙 _
  证明: rfl

@[simp]
-/
theorem pushoutCoconeOfRightIso_inl : (pushoutCoconeOfRightIso f g).inl = 𝟙 _ := rfl

@[simp]
/--
theorem `pushoutCoconeOfRightIso_inr` / 定理 `pushoutCoconeOfRightIso_inr`

English:
theorem pushoutCoconeOfRightIso_inr
  statement: (pushoutCoconeOfRightIso f g).inr = inv g ≫ f
  proof: rfl

中文:
定理 pushoutCoconeOfRightIso_inr
  结论: (pushoutCoconeOfRightIso f g).inr = inv g ≫ f
  证明: rfl
-/
theorem pushoutCoconeOfRightIso_inr : (pushoutCoconeOfRightIso f g).inr = inv g ≫ f := rfl

/--
theorem `pushoutCoconeOfRightIso_ι_app_none` / 定理 `pushoutCoconeOfRightIso_ι_app_none`

English:
theorem pushoutCoconeOfRightIso_ι_app_none
  statement: (pushoutCoconeOfRightIso f g).ι.app none = f
  proof: by
  simp

@[simp]

中文:
定理 pushoutCoconeOfRightIso_ι_app_none
  结论: (pushoutCoconeOfRightIso f g).ι.app none = f
  证明: by
  simp

@[simp]
-/
theorem pushoutCoconeOfRightIso_ι_app_none : (pushoutCoconeOfRightIso f g).ι.app none = f := by
  simp

@[simp]
/--
theorem `pushoutCoconeOfRightIso_ι_app_left` / 定理 `pushoutCoconeOfRightIso_ι_app_left`

English:
theorem pushoutCoconeOfRightIso_ι_app_left
  statement: (pushoutCoconeOfRightIso f g).ι.app left = 𝟙 _
  proof: rfl

@[simp]

中文:
定理 pushoutCoconeOfRightIso_ι_app_left
  结论: (pushoutCoconeOfRightIso f g).ι.app left = 𝟙 _
  证明: rfl

@[simp]
-/
theorem pushoutCoconeOfRightIso_ι_app_left : (pushoutCoconeOfRightIso f g).ι.app left = 𝟙 _ := rfl

@[simp]
/--
theorem `pushoutCoconeOfRightIso_ι_app_right` / 定理 `pushoutCoconeOfRightIso_ι_app_right`

English:
theorem pushoutCoconeOfRightIso_ι_app_right
  proof: rfl

中文:
定理 pushoutCoconeOfRightIso_ι_app_right
  证明: rfl
-/
theorem pushoutCoconeOfRightIso_ι_app_right :
    (pushoutCoconeOfRightIso f g).ι.app right = inv g ≫ f := rfl

/--
Definition of `pushoutCoconeOfRightIsoIsLimit` / `pushoutCoconeOfRightIsoIsLimit` 的定义

English:
definition pushoutCoconeOfRightIsoIsLimit
  signature: : IsColimit (pushoutCoconeOfRightIso f g)
  body: PushoutCocone.isColimitAux' _ fun s => ⟨s.inl, by simp [← s.condition]⟩

中文:
定义 pushoutCoconeOfRightIsoIsLimit
  签名: : 是余极限 (pushoutCoconeOfRightIso f g)
  定义体: PushoutCocone.isColimitAux' _ fun s => ⟨s.inl, by simp [← s.condition]⟩

Depends on / 依赖: PushoutCocone, PushoutCocone.isColimitAux, condition, isColimitAux, s.condition, s.inl
-/
def pushoutCoconeOfRightIsoIsLimit : IsColimit (pushoutCoconeOfRightIso f g) :=
  PushoutCocone.isColimitAux' _ fun s => ⟨s.inl, by simp [← s.condition]⟩

/--
theorem `hasPushout_of_right_iso` / 定理 `hasPushout_of_right_iso`

English:
theorem hasPushout_of_right_iso
  statement: HasPushout f g
  proof: ⟨⟨⟨_, pushoutCoconeOfRightIsoIsLimit f g⟩⟩⟩

中文:
定理 hasPushout_of_right_iso
  结论: HasPushout f g
  证明: ⟨⟨⟨_, pushoutCoconeOfRightIsoIsLimit f g⟩⟩⟩

Depends on / 依赖: pushoutCoconeOfRightIsoIsLimit
-/
theorem hasPushout_of_right_iso : HasPushout f g :=
  ⟨⟨⟨_, pushoutCoconeOfRightIsoIsLimit f g⟩⟩⟩

attribute [local instance] hasPushout_of_right_iso

set_option backward.isDefEq.respectTransparency false in
/--
Instance `pushout_inl_iso_of_right_iso` / 实例 `pushout_inl_iso_of_right_iso`

English:
instance pushout_inl_iso_of_right_iso
  signature: : IsIso (pushout.inl _ _ : _ ⟶ pushout f g)
  body: by
  refine ⟨⟨pushout.desc (𝟙 _) (inv g ≫ f) (by simp), by simp, ?_⟩⟩
  ext
  · simp
  · simp [pushout.condition]

@[reassoc (attr := simp)]

中文:
实例 pushout_inl_iso_of_right_iso
  签名: : 是同构 (pushout.inl _ _ : _ ⟶ pushout f g)
  定义体: by
  refine ⟨⟨pushout.desc (𝟙 _) (inv g ≫ f) (by simp), by simp, ?_⟩⟩
  ext
  · simp
  · simp [pushout.condition]

@[reassoc (attr := simp)]

Depends on / 依赖: condition, pushout, pushout.condition, pushout.desc
-/
instance pushout_inl_iso_of_right_iso : IsIso (pushout.inl _ _ : _ ⟶ pushout f g) := by
  refine ⟨⟨pushout.desc (𝟙 _) (inv g ≫ f) (by simp), by simp, ?_⟩⟩
  ext
  · simp
  · simp [pushout.condition]

@[reassoc (attr := simp)]
/--
lemma `pushout_inr_inv_inl_of_right_isIso` / 引理 `pushout_inr_inv_inl_of_right_isIso`

English:
lemma pushout_inr_inv_inl_of_right_isIso
  proof: by
  rw [IsIso.eq_inv_comp]; rw [← pushout.condition_assoc]; rw [IsIso.hom_inv_id]; rw [Category.comp_id]

中文:
引理 pushout_inr_inv_inl_of_right_isIso
  证明: by
  rw [IsIso.eq_inv_comp]; rw [← pushout.condition_assoc]; rw [IsIso.hom_inv_id]; rw [Category.comp_id]

Depends on / 依赖: Category, Category.comp_id, IsIso.eq_inv_comp, IsIso.hom_inv_id, comp_id, condition_assoc, eq_inv_comp, hom_inv_id, pushout, pushout.condition_assoc
-/
lemma pushout_inr_inv_inl_of_right_isIso :
    pushout.inr f g ≫ inv (pushout.inl f g) = inv g ≫ f := by
  rw [IsIso.eq_inv_comp]; rw [← pushout.condition_assoc]; rw [IsIso.hom_inv_id]; rw [Category.comp_id]

end PushoutRightIso


end CategoryTheory.Limits
