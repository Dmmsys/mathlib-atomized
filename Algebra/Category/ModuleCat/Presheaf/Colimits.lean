/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! # Colimits in categories of presheaves of modules

In this file, it is shown that under suitable assumptions,
colimits exist in the category `PresheafOfModules R`.

-/

@[expose] public section

universe v v₁ v₂ u₁ u₂ u u'

open CategoryTheory Category Limits

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {J : Type u₂} [Category.{v₂} J]
  (F : J ⥤ PresheafOfModules.{v} R)

section Colimits

variable [forall {X Y : Cᵒᵖ} (f : X ⟶ Y), PreservesColimit (F ⋙ evaluation R Y)
  (ModuleCat.restrictScalars (R.map f).hom)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `evaluationJointlyReflectsColimits` / `evaluationJointlyReflectsColimits` 的定义

English:
definition evaluationJointlyReflectsColimits
  signature: (c : Cocone F)
  body: { app := fun X => (hc X).desc ((evaluation R X).mapCocone s)
      naturality := fun {X Y} f => (hc X).hom_ext (fun j => by
        rw [(hc X).fac_assoc ((evaluation R X).mapCocone s) j]
        have h₁ := (c.ι.app j).naturality f
        have h₂ := (hc Y).fac ((evaluation R Y).mapCocone s)
        

中文:
定义 evaluationJointlyReflectsColimits
  签名: (c : Cocone F)
  定义体: { app := fun X => (hc X).desc ((evaluation R X).mapCocone s)
      naturality := fun {X Y} f => (hc X).hom_ext (fun j => by
        rw [(hc X).fac_assoc ((evaluation R X).mapCocone s) j]
        have h₁ := (c.ι.app j).naturality f
        have h₂ := (hc Y).fac ((evaluation R Y).mapCocone s)
        

Depends on / 依赖: Functor, Functor.map_comp, Hom.naturality, evaluation, fac_assoc, hom_ext, mapCocone, map_comp, naturality, reassoc_of
-/
def evaluationJointlyReflectsColimits (c : Cocone F)
    (hc : forall (X : Cᵒᵖ), IsColimit ((evaluation R X).mapCocone c)) : IsColimit c where
  desc s :=
    { app := fun X => (hc X).desc ((evaluation R X).mapCocone s)
      naturality := fun {X Y} f => (hc X).hom_ext (fun j => by
        rw [(hc X).fac_assoc ((evaluation R X).mapCocone s) j]
        have h₁ := (c.ι.app j).naturality f
        have h₂ := (hc Y).fac ((evaluation R Y).mapCocone s)
        dsimp at h₁ h₂ ⊢
        simp only [← reassoc_of% h₁, ← Functor.map_comp, h₂, Hom.naturality]) }
  fac s j := by
    ext1 X
    exact (hc X).fac ((evaluation R X).mapCocone s) j
  uniq s m hm := by
    ext1 X
    apply (hc X).uniq ((evaluation R X).mapCocone s)
    intro j
    dsimp
    rw [← hm]
    rfl

variable [forall X, HasColimit (F ⋙ evaluation R X)]

instance {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    HasColimit (F ⋙ evaluation R Y ⋙ (ModuleCat.restrictScalars (R.map f).hom)) :=
  ⟨_, isColimitOfPreserves (ModuleCat.restrictScalars (R.map f).hom)
    (colimit.isColimit (F ⋙ evaluation R Y))⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given `F : J ⥤ PresheafOfModules.{v} R`, this is the presheaf of modules obtained by
taking a colimit in the category of modules over `R.obj X` for all `X`. -/
@[simps]
/--
Definition of `colimitPresheafOfModules` / `colimitPresheafOfModules` 的定义

English:
definition colimitPresheafOfModules
  signature: : PresheafOfModules R where
  body: colimit (F ⋙ evaluation R X)
  map {_ Y} f := colimMap (Functor.whiskerLeft F (restriction R f)) ≫
    (preservesColimitIso (ModuleCat.restrictScalars (R.map f).hom) (F ⋙ evaluation R Y)).inv
  map_id X := colimit.hom_ext (fun j => by
    dsimp
    rw [ι_colimMap_assoc]; rw [Functor.whiskerLeft_app]

中文:
定义 colimitPresheafOfModules
  签名: : PresheafOfModules R where
  定义体: colimit (F ⋙ evaluation R X)
  map {_ Y} f := colimMap (Functor.whiskerLeft F (restriction R f)) ≫
    (preservesColimitIso (ModuleCat.restrictScalars (R.map f).hom) (F ⋙ evaluation R Y)).inv
  map_id X := colimit.hom_ext (fun j => by
    dsimp
    rw [ι_colimMap_assoc]; rw [Functor.whiskerLeft_app]

Depends on / 依赖: colimit, evaluation
-/
noncomputable def colimitPresheafOfModules : PresheafOfModules R where
  obj X := colimit (F ⋙ evaluation R X)
  map {_ Y} f := colimMap (Functor.whiskerLeft F (restriction R f)) ≫
    (preservesColimitIso (ModuleCat.restrictScalars (R.map f).hom) (F ⋙ evaluation R Y)).inv
  map_id X := colimit.hom_ext (fun j => by
    dsimp
    rw [ι_colimMap_assoc]; rw [Functor.whiskerLeft_app]; rw [restriction_app]
    -- Here we should rewrite using `Functor.assoc` but that gives a "motive is type-incorrect"
    erw [ι_preservesColimitIso_inv (G := ModuleCat.restrictScalars (R.map (𝟙 X)).hom)]
    rw [ModuleCat.restrictScalarsId'App_inv_naturality]; rw [map_id]
    dsimp)
  map_comp {X Y Z} f g := colimit.hom_ext (fun j => by
    dsimp
    rw [ι_colimMap_assoc]; rw [Functor.whiskerLeft_app]; rw [restriction_app]; rw [assoc]; rw [ι_colimMap_assoc]
    -- Here we should rewrite using `Functor.assoc` but that gives a "motive is type-incorrect"
    erw [ι_preservesColimitIso_inv (G := ModuleCat.restrictScalars (R.map (f ≫ g)).hom),
      ι_preservesColimitIso_inv_assoc (G := ModuleCat.restrictScalars (R.map f).hom)]
    rw [← Functor.map_comp_assoc]; rw [ι_colimMap_assoc]
    erw [ι_preservesColimitIso_inv (G := ModuleCat.restrictScalars (R.map g).hom)]
    rw [map_comp]; rw [ModuleCat.restrictScalarsComp'_inv_app]; rw [assoc]; rw [assoc]; rw [Functor.whiskerLeft_app]; rw [Functor.whiskerLeft_app]; rw [restriction_app]; rw [restriction_app]
    simp only [Functor.map_comp, assoc]
    rfl)

set_option backward.defeqAttrib.useBackward true in
/-- The (colimit) cocone for `F : J ⥤ PresheafOfModules.{v} R` that is constructed from
the colimit of `F ⋙ evaluation R X` for all `X`. -/
@[simps]
/--
Definition of `colimitCocone` / `colimitCocone` 的定义

English:
definition colimitCocone
  signature: : Cocone F where
  body: colimitPresheafOfModules F
  ι :=
    { app := fun j =>
        { app := fun X => colimit.ι (F ⋙ evaluation R X) j
          naturality := fun {X Y} f => by
            dsimp
            erw [colimit.ι_desc_assoc, assoc, ← ι_preservesColimitIso_inv]
            rfl }
      naturality := fun {X Y} f 

中文:
定义 colimitCocone
  签名: : Cocone F where
  定义体: colimitPresheafOfModules F
  ι :=
    { app := fun j =>
        { app := fun X => colimit.ι (F ⋙ evaluation R X) j
          naturality := fun {X Y} f => by
            dsimp
            erw [colimit.ι_desc_assoc, assoc, ← ι_preservesColimitIso_inv]
            rfl }
      naturality := fun {X Y} f 

Depends on / 依赖: colimitPresheafOfModules
-/
noncomputable def colimitCocone : Cocone F where
  pt := colimitPresheafOfModules F
  ι :=
    { app := fun j =>
        { app := fun X => colimit.ι (F ⋙ evaluation R X) j
          naturality := fun {X Y} f => by
            dsimp
            erw [colimit.ι_desc_assoc, assoc, ← ι_preservesColimitIso_inv]
            rfl }
      naturality := fun {X Y} f => by
        ext1 X
        simpa using colimit.w (F ⋙ evaluation R X) f }

/--
Definition of `isColimitColimitCocone` / `isColimitColimitCocone` 的定义

English:
definition isColimitColimitCocone
  signature: : IsColimit (colimitCocone F)
  body: evaluationJointlyReflectsColimits _ _ (fun _ => colimit.isColimit _)

中文:
定义 isColimitColimitCocone
  签名: : IsColimit (colimitCocone F)
  定义体: evaluationJointlyReflectsColimits _ _ (fun _ => colimit.isColimit _)

Depends on / 依赖: colimit, colimit.isColimit, evaluationJointlyReflectsColimits, isColimit
-/
noncomputable def isColimitColimitCocone : IsColimit (colimitCocone F) :=
  evaluationJointlyReflectsColimits _ _ (fun _ => colimit.isColimit _)

/--
Instance `hasColimit` / 实例 `hasColimit`

English:
instance hasColimit
  signature: : HasColimit F
  body: ⟨_, isColimitColimitCocone F⟩

中文:
实例 hasColimit
  签名: : HasColimit F
  定义体: ⟨_, isColimitColimitCocone F⟩

Depends on / 依赖: isColimitColimitCocone
-/
instance hasColimit : HasColimit F := ⟨_, isColimitColimitCocone F⟩

/--
Instance `evaluation_preservesColimit` / 实例 `evaluation_preservesColimit`

English:
instance evaluation_preservesColimit
  signature: (X : Cᵒᵖ)
  body: preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F) (colimit.isColimit _)

中文:
实例 evaluation_preservesColimit
  签名: (X : Cᵒᵖ)
  定义体: preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F) (colimit.isColimit _)

Depends on / 依赖: colimit, colimit.isColimit, isColimit, isColimitColimitCocone, preservesColimit_of_preserves_colimit_cocone
-/
instance evaluation_preservesColimit (X : Cᵒᵖ) :
    PreservesColimit F (evaluation R X) :=
  preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F) (colimit.isColimit _)

variable [forall X, PreservesColimit F
  (evaluation R X ⋙ forget₂ (ModuleCat (R.obj X)) AddCommGrpCat)]

/--
Instance `toPresheaf_preservesColimit` / 实例 `toPresheaf_preservesColimit`

English:
instance toPresheaf_preservesColimit
  signature: :
  body: preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F)
    (Limits.evaluationJointlyReflectsColimits _
      (fun X => isColimitOfPreserves (evaluation R X ⋙ forget₂ _ AddCommGrpCat)
        (isColimitColimitCocone F)))

中文:
实例 toPresheaf_preservesColimit
  签名: :
  定义体: preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F)
    (Limits.evaluationJointlyReflectsColimits _
      (fun X => isColimitOfPreserves (evaluation R X ⋙ forget₂ _ AddCommGrpCat)
        (isColimitColimitCocone F)))

Depends on / 依赖: AddCommGrpCat, Limits, Limits.evaluationJointlyReflectsColimits, evaluation, evaluationJointlyReflectsColimits, isColimitColimitCocone, isColimitOfPreserves, preservesColimit_of_preserves_colimit_cocone
-/
instance toPresheaf_preservesColimit :
    PreservesColimit F (toPresheaf R) :=
  preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F)
    (Limits.evaluationJointlyReflectsColimits _
      (fun X => isColimitOfPreserves (evaluation R X ⋙ forget₂ _ AddCommGrpCat)
        (isColimitColimitCocone F)))

end Colimits

variable (R J)

section HasColimitsOfShape

variable [HasColimitsOfShape J AddCommGrpCat.{v}]

/--
Instance `hasColimitsOfShape` / 实例 `hasColimitsOfShape`

English:
instance hasColimitsOfShape
  signature: : HasColimitsOfShape J (PresheafOfModules.{v} R) where

中文:
实例 hasColimitsOfShape
  签名: : HasColimitsOfShape J (PresheafOfModules.{v} R) where
-/
instance hasColimitsOfShape : HasColimitsOfShape J (PresheafOfModules.{v} R) where

/--
Instance `evaluation_preservesColimitsOfShape` / 实例 `evaluation_preservesColimitsOfShape`

English:
instance evaluation_preservesColimitsOfShape
  signature: (X : Cᵒᵖ)

中文:
实例 evaluation_preservesColimitsOfShape
  签名: (X : Cᵒᵖ)
-/
noncomputable instance evaluation_preservesColimitsOfShape (X : Cᵒᵖ) :
    PreservesColimitsOfShape J (evaluation R X : PresheafOfModules.{v} R ⥤ _) where

/--
Instance `toPresheaf_preservesColimitsOfShape` / 实例 `toPresheaf_preservesColimitsOfShape`

English:
instance toPresheaf_preservesColimitsOfShape
  signature: :

中文:
实例 toPresheaf_preservesColimitsOfShape
  签名: :
-/
noncomputable instance toPresheaf_preservesColimitsOfShape :
    PreservesColimitsOfShape J (toPresheaf.{v} R) where

end HasColimitsOfShape

namespace Finite

/--
Instance `hasFiniteColimits` / 实例 `hasFiniteColimits`

English:
instance hasFiniteColimits
  signature: : HasFiniteColimits (PresheafOfModules.{v} R)
  body: ⟨fun _ => inferInstance⟩

中文:
实例 hasFiniteColimits
  签名: : HasFiniteColimits (PresheafOfModules.{v} R)
  定义体: ⟨fun _ => inferInstance⟩
-/
instance hasFiniteColimits : HasFiniteColimits (PresheafOfModules.{v} R) :=
  ⟨fun _ => inferInstance⟩

/--
Instance `evaluation_preservesFiniteColimits` / 实例 `evaluation_preservesFiniteColimits`

English:
instance evaluation_preservesFiniteColimits
  signature: (X : Cᵒᵖ)

中文:
实例 evaluation_preservesFiniteColimits
  签名: (X : Cᵒᵖ)
-/
noncomputable instance evaluation_preservesFiniteColimits (X : Cᵒᵖ) :
    PreservesFiniteColimits (evaluation.{v} R X) where

/--
Instance `toPresheaf_preservesFiniteColimits` / 实例 `toPresheaf_preservesFiniteColimits`

English:
instance toPresheaf_preservesFiniteColimits
  signature: :

中文:
实例 toPresheaf_preservesFiniteColimits
  签名: :
-/
noncomputable instance toPresheaf_preservesFiniteColimits :
    PreservesFiniteColimits (toPresheaf R) where

end Finite

section HasColimitsOfSize

variable [HasColimitsOfSize.{v₂, u₂} AddCommGrpCat.{v}]

/--
Instance `hasColimitsOfSize` / 实例 `hasColimitsOfSize`

English:
instance hasColimitsOfSize
  signature: : HasColimitsOfSize.{v₂, u₂} (PresheafOfModules.{v} R) where

中文:
实例 hasColimitsOfSize
  签名: : HasColimitsOfSize.{v₂, u₂} (PresheafOfModules.{v} R) where
-/
instance hasColimitsOfSize : HasColimitsOfSize.{v₂, u₂} (PresheafOfModules.{v} R) where

/--
Instance `evaluation_preservesColimitsOfSize` / 实例 `evaluation_preservesColimitsOfSize`

English:
instance evaluation_preservesColimitsOfSize
  signature: (X : Cᵒᵖ)

中文:
实例 evaluation_preservesColimitsOfSize
  签名: (X : Cᵒᵖ)
-/
noncomputable instance evaluation_preservesColimitsOfSize (X : Cᵒᵖ) :
    PreservesColimitsOfSize.{v₂, u₂} (evaluation R X : PresheafOfModules.{v} R ⥤ _) where

/--
Instance `toPresheaf_preservesColimitsOfSize` / 实例 `toPresheaf_preservesColimitsOfSize`

English:
instance toPresheaf_preservesColimitsOfSize
  signature: :

中文:
实例 toPresheaf_preservesColimitsOfSize
  签名: :
-/
noncomputable instance toPresheaf_preservesColimitsOfSize :
    PreservesColimitsOfSize.{v₂, u₂} (toPresheaf.{v} R) where

end HasColimitsOfSize

end PresheafOfModules
