/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Limits in categories of presheaves of modules

In this file, it is shown that under suitable assumptions,
limits exist in the category `PresheafOfModules R`.

-/

@[expose] public section

universe v v₁ v₂ u₁ u₂ u u'

open CategoryTheory Category Limits

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {J : Type u₂} [Category.{v₂} J]
  (F : J ⥤ PresheafOfModules.{v} R)

section Limits

variable [forall X, Small.{v} ((F ⋙ evaluation R X) ⋙ forget _).sections]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `evaluationJointlyReflectsLimits` / `evaluationJointlyReflectsLimits` 的定义

English:
definition evaluationJointlyReflectsLimits
  signature: (c : Cone F)
  body: { app := fun X => (hc X).lift ((evaluation R X).mapCone s)
      naturality := fun {X Y} f => by
        apply (isLimitOfPreserves (ModuleCat.restrictScalars (R.map f).hom) (hc Y)).hom_ext
        intro j
        have h₁ := (c.π.app j).naturality f
        have h₂ := (hc X).fac ((evaluation R X).mapCone s) j
        rw [Functor.mapCone_π_app]; rw [assoc]; rw [assoc]; rw [← Functor.map_comp]; rw [IsLimit.fac]
        dsimp at h₁ h₂ ⊢
        rw [h₁]; rw [reassoc_of% h₂]; rw [Hom.naturality] }
  fac s j := by
    ext1 X
    exact (hc X).fac ((evaluation R X).mapCone s) j
  uniq s m hm := by
    ext1 X
    apply (hc X).uniq ((evaluation R X).mapCone s)
    intro j
    dsimp
    rw [← hm]; rw [comp_app]

中文:
定义 evaluationJointlyReflectsLimits
  签名: (c : 锥 F)
  定义体: { app := fun X => (hc X).lift ((evaluation R X).mapCone s)
      naturality := fun {X Y} f => by
        apply (isLimitOfPreserves (ModuleCat.restrictScalars (R.map f).hom) (hc Y)).hom_ext
        intro j
        have h₁ := (c.π.app j).naturality f
        have h₂ := (hc X).fac ((evaluation R X).mapCone s) j
        rw [Functor.mapCone_π_app]; rw [assoc]; rw [assoc]; rw [← Functor.map_comp]; rw [IsLimit.fac]
        dsimp at h₁ h₂ ⊢
        rw [h₁]; rw [reassoc_of% h₂]; rw [Hom.naturality] }
  fac s j := by
    ext1 X
    exact (hc X).fac ((evaluation R X).mapCone s) j
  uniq s m hm := by
    ext1 X
    apply (hc X).uniq ((evaluation R X).mapCone s)
    intro j
    dsimp
    rw [← hm]; rw [comp_app]

Depends on / 依赖: Functor, Functor.mapCone_, Functor.map_comp, Hom.naturality, IsLimit, IsLimit.fac, ModuleCat, ModuleCat.restrictScalars, R.map, evaluation, hom_ext, isLimitOfPreserves, mapCone, map_comp, naturality, reassoc_of, restrictScalars
-/
def evaluationJointlyReflectsLimits (c : Cone F)
    (hc : forall (X : Cᵒᵖ), IsLimit ((evaluation R X).mapCone c)) : IsLimit c where
  lift s :=
    { app := fun X => (hc X).lift ((evaluation R X).mapCone s)
      naturality := fun {X Y} f => by
        apply (isLimitOfPreserves (ModuleCat.restrictScalars (R.map f).hom) (hc Y)).hom_ext
        intro j
        have h₁ := (c.π.app j).naturality f
        have h₂ := (hc X).fac ((evaluation R X).mapCone s) j
        rw [Functor.mapCone_π_app]; rw [assoc]; rw [assoc]; rw [← Functor.map_comp]; rw [IsLimit.fac]
        dsimp at h₁ h₂ ⊢
        rw [h₁]; rw [reassoc_of% h₂]; rw [Hom.naturality] }
  fac s j := by
    ext1 X
    exact (hc X).fac ((evaluation R X).mapCone s) j
  uniq s m hm := by
    ext1 X
    apply (hc X).uniq ((evaluation R X).mapCone s)
    intro j
    dsimp
    rw [← hm]; rw [comp_app]

instance {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    HasLimit (F ⋙ evaluation R Y ⋙ ModuleCat.restrictScalars (R.map f).hom) := by
  change HasLimit ((F ⋙ evaluation R Y) ⋙ ModuleCat.restrictScalars (R.map f).hom)
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given `F : J ⥤ PresheafOfModules.{v} R`, this is the presheaf of modules obtained by
taking a limit in the category of modules over `R.obj X` for all `X`. -/
@[simps]
/--
Definition of `limitPresheafOfModules` / `limitPresheafOfModules` 的定义

English:
definition limitPresheafOfModules
  signature: : PresheafOfModules R where
  body: limit (F ⋙ evaluation R X)
  map {_ Y} f := limMap (Functor.whiskerLeft F (restriction R f)) ≫
    (preservesLimitIso (ModuleCat.restrictScalars (R.map f).hom) (F ⋙ evaluation R Y)).inv
  map_id X := by
    dsimp
    rw [← cancel_mono (preservesLimitIso _ _).hom]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]
    apply limit.hom_ext
    simp [← Functor.assoc, ← ModuleCat.restrictScalarsId'App_inv_naturality,
      ModuleCat.restrictScalarsId'_inv_app]
  map_comp {X Y Z} f g := by
    dsimp
    rw [← cancel_mono (preservesLimitIso _ _).hom]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]
    apply limit.hom_ext
    intro j
    simp only [Functor.map_comp, assoc, ← Functor.assoc, preservesLimitIso_hom_π,
      ← ModuleCat.restrictScalarsComp'App_inv_naturality]
    rw [← Functor.map_comp_assoc]; rw [← Functor.map_comp_assoc]; rw [assoc]; rw [preservesLimitIso_inv_π]
    simp

中文:
定义 limitPresheafOfModules
  签名: : 预模层 R where
  定义体: limit (F ⋙ evaluation R X)
  map {_ Y} f := limMap (Functor.whiskerLeft F (restriction R f)) ≫
    (preservesLimitIso (ModuleCat.restrictScalars (R.map f).hom) (F ⋙ evaluation R Y)).inv
  map_id X := by
    dsimp
    rw [← cancel_mono (preservesLimitIso _ _).hom]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]
    apply limit.hom_ext
    simp [← Functor.assoc, ← ModuleCat.restrictScalarsId'App_inv_naturality,
      ModuleCat.restrictScalarsId'_inv_app]
  map_comp {X Y Z} f g := by
    dsimp
    rw [← cancel_mono (preservesLimitIso _ _).hom]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]
    apply limit.hom_ext
    intro j
    simp only [Functor.map_comp, assoc, ← Functor.assoc, preservesLimitIso_hom_π,
      ← ModuleCat.restrictScalarsComp'App_inv_naturality]
    rw [← Functor.map_comp_assoc]; rw [← Functor.map_comp_assoc]; rw [assoc]; rw [preservesLimitIso_inv_π]
    simp

Depends on / 依赖: evaluation
-/
noncomputable def limitPresheafOfModules : PresheafOfModules R where
  obj X := limit (F ⋙ evaluation R X)
  map {_ Y} f := limMap (Functor.whiskerLeft F (restriction R f)) ≫
    (preservesLimitIso (ModuleCat.restrictScalars (R.map f).hom) (F ⋙ evaluation R Y)).inv
  map_id X := by
    dsimp
    rw [← cancel_mono (preservesLimitIso _ _).hom]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]
    apply limit.hom_ext
    simp [← Functor.assoc, ← ModuleCat.restrictScalarsId'App_inv_naturality,
      ModuleCat.restrictScalarsId'_inv_app]
  map_comp {X Y Z} f g := by
    dsimp
    rw [← cancel_mono (preservesLimitIso _ _).hom]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]
    apply limit.hom_ext
    intro j
    simp only [Functor.map_comp, assoc, ← Functor.assoc, preservesLimitIso_hom_π,
      ← ModuleCat.restrictScalarsComp'App_inv_naturality]
    rw [← Functor.map_comp_assoc]; rw [← Functor.map_comp_assoc]; rw [assoc]; rw [preservesLimitIso_inv_π]
    simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The (limit) cone for `F : J ⥤ PresheafOfModules.{v} R` that is constructed from the limit
of `F ⋙ evaluation R X` for all `X`. -/
@[simps]
/--
Definition of `limitCone` / `limitCone` 的定义

English:
definition limitCone
  signature: : Cone F where
  body: limitPresheafOfModules F
  π :=
    { app := fun j =>
        { app := fun X => limit.π (F ⋙ evaluation R X) j
          naturality := fun {X Y} f => by
            dsimp
            simp only [assoc, preservesLimitIso_inv_π]
            apply limMap_π }
      naturality := fun {j j'} f => by
        ext1 X
        simpa using (limit.w (F ⋙ evaluation R X) f).symm }

中文:
定义 limitCone
  签名: : 锥 F where
  定义体: limitPresheafOfModules F
  π :=
    { app := fun j =>
        { app := fun X => limit.π (F ⋙ evaluation R X) j
          naturality := fun {X Y} f => by
            dsimp
            simp only [assoc, preservesLimitIso_inv_π]
            apply limMap_π }
      naturality := fun {j j'} f => by
        ext1 X
        simpa using (limit.w (F ⋙ evaluation R X) f).symm }

Depends on / 依赖: limitPresheafOfModules
-/
noncomputable def limitCone : Cone F where
  pt := limitPresheafOfModules F
  π :=
    { app := fun j =>
        { app := fun X => limit.π (F ⋙ evaluation R X) j
          naturality := fun {X Y} f => by
            dsimp
            simp only [assoc, preservesLimitIso_inv_π]
            apply limMap_π }
      naturality := fun {j j'} f => by
        ext1 X
        simpa using (limit.w (F ⋙ evaluation R X) f).symm }

/--
Definition of `isLimitLimitCone` / `isLimitLimitCone` 的定义

English:
definition isLimitLimitCone
  signature: : IsLimit (limitCone F)
  body: evaluationJointlyReflectsLimits _ _ (fun _ => limit.isLimit _)

中文:
定义 isLimitLimitCone
  签名: : 是极限 (limitCone F)
  定义体: evaluationJointlyReflectsLimits _ _ (fun _ => limit.isLimit _)

Depends on / 依赖: evaluationJointlyReflectsLimits, isLimit, limit.isLimit
-/
noncomputable def isLimitLimitCone : IsLimit (limitCone F) :=
  evaluationJointlyReflectsLimits _ _ (fun _ => limit.isLimit _)

/--
Instance `hasLimit` / 实例 `hasLimit`

English:
instance hasLimit
  signature: : HasLimit F
  body: ⟨_, isLimitLimitCone F⟩

中文:
实例 hasLimit
  签名: : 有极限 F
  定义体: ⟨_, isLimitLimitCone F⟩

Depends on / 依赖: isLimitLimitCone
-/
instance hasLimit : HasLimit F := ⟨_, isLimitLimitCone F⟩

/--
Instance `evaluation_preservesLimit` / 实例 `evaluation_preservesLimit`

English:
instance evaluation_preservesLimit
  signature: (X : Cᵒᵖ)
  body: preservesLimit_of_preserves_limit_cone (isLimitLimitCone F) (limit.isLimit _)

中文:
实例 evaluation_preservesLimit
  签名: (X : Cᵒᵖ)
  定义体: preservesLimit_of_preserves_limit_cone (isLimitLimitCone F) (limit.isLimit _)

Depends on / 依赖: isLimit, isLimitLimitCone, limit.isLimit, preservesLimit_of_preserves_limit_cone
-/
noncomputable instance evaluation_preservesLimit (X : Cᵒᵖ) :
    PreservesLimit F (evaluation R X) :=
  preservesLimit_of_preserves_limit_cone (isLimitLimitCone F) (limit.isLimit _)

/--
Instance `toPresheaf_preservesLimit` / 实例 `toPresheaf_preservesLimit`

English:
instance toPresheaf_preservesLimit
  signature: :
  body: preservesLimit_of_preserves_limit_cone (isLimitLimitCone F)
    (Limits.evaluationJointlyReflectsLimits _
      (fun X => isLimitOfPreserves (evaluation R X ⋙ forget₂ _ AddCommGrpCat)
        (isLimitLimitCone F)))

中文:
实例 toPresheaf_preservesLimit
  签名: :
  定义体: preservesLimit_of_preserves_limit_cone (isLimitLimitCone F)
    (Limits.evaluationJointlyReflectsLimits _
      (fun X => isLimitOfPreserves (evaluation R X ⋙ forget₂ _ AddCommGrpCat)
        (isLimitLimitCone F)))

Depends on / 依赖: AddCommGrpCat, Limits, Limits.evaluationJointlyReflectsLimits, evaluation, evaluationJointlyReflectsLimits, isLimitLimitCone, isLimitOfPreserves, preservesLimit_of_preserves_limit_cone
-/
noncomputable instance toPresheaf_preservesLimit :
    PreservesLimit F (toPresheaf R) :=
  preservesLimit_of_preserves_limit_cone (isLimitLimitCone F)
    (Limits.evaluationJointlyReflectsLimits _
      (fun X => isLimitOfPreserves (evaluation R X ⋙ forget₂ _ AddCommGrpCat)
        (isLimitLimitCone F)))

end Limits

variable (R J)

section Small

variable [Small.{v} J]

/--
Instance `hasLimitsOfShape` / 实例 `hasLimitsOfShape`

English:
instance hasLimitsOfShape
  signature: : HasLimitsOfShape J (PresheafOfModules.{v} R) where

中文:
实例 hasLimitsOfShape
  签名: : 有形状极限 J (预模层.{v} R) where
-/
instance hasLimitsOfShape : HasLimitsOfShape J (PresheafOfModules.{v} R) where
/--
Instance `hasLimitsOfSize` / 实例 `hasLimitsOfSize`

English:
instance hasLimitsOfSize
  signature: : HasLimitsOfSize.{v, v} (PresheafOfModules.{v} R) where

中文:
实例 hasLimitsOfSize
  签名: : 有LimitsOfSize.{v, v} (预模层.{v} R) where
-/
instance hasLimitsOfSize : HasLimitsOfSize.{v, v} (PresheafOfModules.{v} R) where

instance (X : Cᵒᵖ) : PreservesLimitsOfShape J (evaluation.{v} R X) where
instance (X : Cᵒᵖ) : PreservesLimitsOfSize.{v, v} (evaluation.{v} R X) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimitsOfShape J (toPresheaf.{v} R)

中文:
实例 :
  签名: 保持形状极限 J (toPresheaf.{v} R)
-/
instance : PreservesLimitsOfShape J (toPresheaf.{v} R) where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimitsOfSize.{v, v} (toPresheaf.{v} R)

中文:
实例 :
  签名: 保持LimitsOfSize.{v, v} (toPresheaf.{v} R)
-/
instance : PreservesLimitsOfSize.{v, v} (toPresheaf.{v} R) where

end Small

section Finite

/--
Instance `hasFiniteLimits` / 实例 `hasFiniteLimits`

English:
instance hasFiniteLimits
  signature: : HasFiniteLimits (PresheafOfModules.{v} R)
  body: ⟨fun _ => inferInstance⟩

中文:
实例 hasFiniteLimits
  签名: : 有有限极限 (预模层.{v} R)
  定义体: ⟨fun _ => inferInstance⟩
-/
instance hasFiniteLimits : HasFiniteLimits (PresheafOfModules.{v} R) :=
  ⟨fun _ => inferInstance⟩

/--
Instance `evaluation_preservesFiniteLimits` / 实例 `evaluation_preservesFiniteLimits`

English:
instance evaluation_preservesFiniteLimits
  signature: (X : Cᵒᵖ)

中文:
实例 evaluation_preservesFiniteLimits
  签名: (X : Cᵒᵖ)
-/
noncomputable instance evaluation_preservesFiniteLimits (X : Cᵒᵖ) :
    PreservesFiniteLimits (evaluation.{v} R X) where

/--
Instance `toPresheaf_preservesFiniteLimits` / 实例 `toPresheaf_preservesFiniteLimits`

English:
instance toPresheaf_preservesFiniteLimits
  signature: :

中文:
实例 toPresheaf_preservesFiniteLimits
  签名: :
-/
noncomputable instance toPresheaf_preservesFiniteLimits :
    PreservesFiniteLimits (toPresheaf.{v} R) where

end Finite

end PresheafOfModules
