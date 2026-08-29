/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Sites.CompatiblePlus
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification

/-!

In this file, we prove that sheafification is compatible with functors which
preserve the correct limits and colimits.

-/

@[expose] public section


namespace CategoryTheory.GrothendieckTopology

open CategoryTheory

open CategoryTheory.Limits CategoryTheory.Functor

open Opposite

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {D : Type*} [Category* D]
variable {E : Type*} [Category* E]
variable (F : D ⥤ E)

variable [forall (J : MulticospanShape.{max v u, max v u}), HasLimitsOfShape (WalkingMulticospan J) D]
variable [forall (J : MulticospanShape.{max v u, max v u}), HasLimitsOfShape (WalkingMulticospan J) E]
variable [forall X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
variable [forall X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ E]
variable [forall X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
variable [forall (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F]
variable (P : Cᵒᵖ ⥤ D)

/--
Definition of `sheafifyCompIso` / `sheafifyCompIso` 的定义

English:
definition sheafifyCompIso
  signature: : J.sheafify P ⋙ F ≅ J.sheafify (P ⋙ F)
  body: J.plusCompIso _ _ ≪≫ (J.plusFunctor _).mapIso (J.plusCompIso _ _)

中文:
定义 sheafifyCompIso
  签名: : J.sheafify P ⋙ F ≅ J.sheafify (P ⋙ F)
  定义体: J.plusCompIso _ _ ≪≫ (J.plusFunctor _).mapIso (J.plusCompIso _ _)

Depends on / 依赖: J.plusCompIso, J.plusFunctor, mapIso, plusCompIso, plusFunctor
-/
noncomputable def sheafifyCompIso : J.sheafify P ⋙ F ≅ J.sheafify (P ⋙ F) :=
  J.plusCompIso _ _ ≪≫ (J.plusFunctor _).mapIso (J.plusCompIso _ _)

/--
Definition of `sheafificationWhiskerLeftIso` / `sheafificationWhiskerLeftIso` 的定义

English:
definition sheafificationWhiskerLeftIso
  signature: (P : Cᵒᵖ ⥤ D)
  body: by
  refine J.plusFunctorWhiskerLeftIso _ ≪≫ ?_ ≪≫ associator _ _ _
  refine isoWhiskerRight ?_ _
  exact J.plusFunctorWhiskerLeftIso _

中文:
定义 sheafificationWhiskerLeftIso
  签名: (P : Cᵒᵖ ⥤ D)
  定义体: by
  refine J.plusFunctorWhiskerLeftIso _ ≪≫ ?_ ≪≫ associator _ _ _
  refine isoWhiskerRight ?_ _
  exact J.plusFunctorWhiskerLeftIso _

Depends on / 依赖: J.plusFunctorWhiskerLeftIso, associator, isoWhiskerRight, plusFunctorWhiskerLeftIso
-/
noncomputable def sheafificationWhiskerLeftIso (P : Cᵒᵖ ⥤ D)
    [forall (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [forall (F : D ⥤ E) (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D),
        PreservesLimit (W.index P).multicospan F] :
    (whiskeringLeft _ _ E).obj (J.sheafify P) ≅
    (whiskeringLeft _ _ _).obj P ⋙ J.sheafification E := by
  refine J.plusFunctorWhiskerLeftIso _ ≪≫ ?_ ≪≫ associator _ _ _
  refine isoWhiskerRight ?_ _
  exact J.plusFunctorWhiskerLeftIso _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `sheafificationWhiskerLeftIso_hom_app` / 定理 `sheafificationWhiskerLeftIso_hom_app`

English:
theorem sheafificationWhiskerLeftIso_hom_app
  statement: (P : Cᵒᵖ ⥤ D) (F : D ⥤ E)
  proof: by
  dsimp [sheafificationWhiskerLeftIso, sheafifyCompIso]
  simp only [sheafify, Category.comp_id]

中文:
定理 sheafificationWhiskerLeftIso_hom_app
  结论: (P : Cᵒᵖ ⥤ D) (F : D ⥤ E)
  证明: by
  dsimp [sheafificationWhiskerLeftIso, sheafifyCompIso]
  simp only [sheafify, Category.comp_id]

Depends on / 依赖: Category, Category.comp_id, comp_id, sheafificationWhiskerLeftIso, sheafify, sheafifyCompIso
-/
theorem sheafificationWhiskerLeftIso_hom_app (P : Cᵒᵖ ⥤ D) (F : D ⥤ E)
    [forall (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [forall (F : D ⥤ E) (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D),
        PreservesLimit (W.index P).multicospan F] :
    (sheafificationWhiskerLeftIso J P).hom.app F = (J.sheafifyCompIso F P).hom := by
  dsimp [sheafificationWhiskerLeftIso, sheafifyCompIso]
  simp only [sheafify, Category.comp_id]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `sheafificationWhiskerLeftIso_inv_app` / 定理 `sheafificationWhiskerLeftIso_inv_app`

English:
theorem sheafificationWhiskerLeftIso_inv_app
  statement: (P : Cᵒᵖ ⥤ D) (F : D ⥤ E)
  proof: by
  dsimp [sheafificationWhiskerLeftIso, sheafifyCompIso]
  simp only [sheafify, Category.id_comp]

中文:
定理 sheafificationWhiskerLeftIso_inv_app
  结论: (P : Cᵒᵖ ⥤ D) (F : D ⥤ E)
  证明: by
  dsimp [sheafificationWhiskerLeftIso, sheafifyCompIso]
  simp only [sheafify, Category.id_comp]

Depends on / 依赖: Category, Category.id_comp, id_comp, sheafificationWhiskerLeftIso, sheafify, sheafifyCompIso
-/
theorem sheafificationWhiskerLeftIso_inv_app (P : Cᵒᵖ ⥤ D) (F : D ⥤ E)
    [forall (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [forall (F : D ⥤ E) (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D),
        PreservesLimit (W.index P).multicospan F] :
    (sheafificationWhiskerLeftIso J P).inv.app F = (J.sheafifyCompIso F P).inv := by
  dsimp [sheafificationWhiskerLeftIso, sheafifyCompIso]
  simp only [sheafify, Category.id_comp]

/--
Definition of `sheafificationWhiskerRightIso` / `sheafificationWhiskerRightIso` 的定义

English:
definition sheafificationWhiskerRightIso
  signature: :
  body: by
  refine associator _ _ _ ≪≫ ?_
  refine isoWhiskerLeft (J.plusFunctor D) (J.plusFunctorWhiskerRightIso _) ≪≫ ?_
  refine ?_ ≪≫ associator _ _ _
  refine (associator _ _ _).symm ≪≫ ?_
  exact isoWhiskerRight (J.plusFunctorWhiskerRightIso _) (J.plusFunctor E)

中文:
定义 sheafificationWhiskerRightIso
  签名: :
  定义体: by
  refine associator _ _ _ ≪≫ ?_
  refine isoWhiskerLeft (J.plusFunctor D) (J.plusFunctorWhiskerRightIso _) ≪≫ ?_
  refine ?_ ≪≫ associator _ _ _
  refine (associator _ _ _).symm ≪≫ ?_
  exact isoWhiskerRight (J.plusFunctorWhiskerRightIso _) (J.plusFunctor E)

Depends on / 依赖: J.plusFunctor, J.plusFunctorWhiskerRightIso, associator, isoWhiskerLeft, isoWhiskerRight, plusFunctor, plusFunctorWhiskerRightIso
-/
noncomputable def sheafificationWhiskerRightIso :
    J.sheafification D ⋙ (whiskeringRight _ _ _).obj F ≅
      (whiskeringRight _ _ _).obj F ⋙ J.sheafification E := by
  refine associator _ _ _ ≪≫ ?_
  refine isoWhiskerLeft (J.plusFunctor D) (J.plusFunctorWhiskerRightIso _) ≪≫ ?_
  refine ?_ ≪≫ associator _ _ _
  refine (associator _ _ _).symm ≪≫ ?_
  exact isoWhiskerRight (J.plusFunctorWhiskerRightIso _) (J.plusFunctor E)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `sheafificationWhiskerRightIso_hom_app` / 定理 `sheafificationWhiskerRightIso_hom_app`

English:
theorem sheafificationWhiskerRightIso_hom_app
  proof: by
  dsimp [sheafificationWhiskerRightIso, sheafifyCompIso]
  simp only [sheafify, Category.id_comp, Category.comp_id]

中文:
定理 sheafificationWhiskerRightIso_hom_app
  证明: by
  dsimp [sheafificationWhiskerRightIso, sheafifyCompIso]
  simp only [sheafify, Category.id_comp, Category.comp_id]

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, comp_id, id_comp, sheafificationWhiskerRightIso, sheafify, sheafifyCompIso
-/
theorem sheafificationWhiskerRightIso_hom_app :
    (J.sheafificationWhiskerRightIso F).hom.app P = (J.sheafifyCompIso F P).hom := by
  dsimp [sheafificationWhiskerRightIso, sheafifyCompIso]
  simp only [sheafify, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `sheafificationWhiskerRightIso_inv_app` / 定理 `sheafificationWhiskerRightIso_inv_app`

English:
theorem sheafificationWhiskerRightIso_inv_app
  proof: by
  dsimp [sheafificationWhiskerRightIso, sheafifyCompIso]
  simp only [sheafify, Category.id_comp, Category.comp_id]

中文:
定理 sheafificationWhiskerRightIso_inv_app
  证明: by
  dsimp [sheafificationWhiskerRightIso, sheafifyCompIso]
  simp only [sheafify, Category.id_comp, Category.comp_id]

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, comp_id, id_comp, sheafificationWhiskerRightIso, sheafify, sheafifyCompIso
-/
theorem sheafificationWhiskerRightIso_inv_app :
    (J.sheafificationWhiskerRightIso F).inv.app P = (J.sheafifyCompIso F P).inv := by
  dsimp [sheafificationWhiskerRightIso, sheafifyCompIso]
  simp only [sheafify, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp, reassoc]
/--
theorem `whiskerRight_toSheafify_sheafifyCompIso_hom` / 定理 `whiskerRight_toSheafify_sheafifyCompIso_hom`

English:
theorem whiskerRight_toSheafify_sheafifyCompIso_hom
  proof: by
  dsimp [sheafifyCompIso]
  simp only [toSheafify, sheafify, whiskerRight_comp, Category.assoc]
  slice_lhs 2 3 => rw [plusCompIso_whiskerRight]
  rw [Category.assoc]; rw [← J.plusMap_comp]; rw [whiskerRight_toPlus_comp_plusCompIso_hom]; rw [←
    Category.assoc]; rw [whiskerRight_toPlus_comp_plusCompIso_hom]

@[simp, reassoc]

中文:
定理 whiskerRight_toSheafify_sheafifyCompIso_hom
  证明: by
  dsimp [sheafifyCompIso]
  simp only [toSheafify, sheafify, whiskerRight_comp, Category.assoc]
  slice_lhs 2 3 => rw [plusCompIso_whiskerRight]
  rw [Category.assoc]; rw [← J.plusMap_comp]; rw [whiskerRight_toPlus_comp_plusCompIso_hom]; rw [←
    Category.assoc]; rw [whiskerRight_toPlus_comp_plusCompIso_hom]

@[simp, reassoc]

Depends on / 依赖: Category, Category.assoc, J.plusMap_comp, plusCompIso_whiskerRight, plusMap_comp, sheafify, sheafifyCompIso, slice_lhs, toSheafify, whiskerRight_comp, whiskerRight_toPlus_comp_plusCompIso_hom
-/
theorem whiskerRight_toSheafify_sheafifyCompIso_hom :
    whiskerRight (J.toSheafify _) _ ≫ (J.sheafifyCompIso F P).hom = J.toSheafify _ := by
  dsimp [sheafifyCompIso]
  simp only [toSheafify, sheafify, whiskerRight_comp, Category.assoc]
  slice_lhs 2 3 => rw [plusCompIso_whiskerRight]
  rw [Category.assoc]; rw [← J.plusMap_comp]; rw [whiskerRight_toPlus_comp_plusCompIso_hom]; rw [←
    Category.assoc]; rw [whiskerRight_toPlus_comp_plusCompIso_hom]

@[simp, reassoc]
/--
theorem `toSheafify_comp_sheafifyCompIso_inv` / 定理 `toSheafify_comp_sheafifyCompIso_inv`

English:
theorem toSheafify_comp_sheafifyCompIso_inv
  proof: by
  rw [Iso.comp_inv_eq]; simp

中文:
定理 toSheafify_comp_sheafifyCompIso_inv
  证明: by
  rw [Iso.comp_inv_eq]; simp

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq
-/
theorem toSheafify_comp_sheafifyCompIso_inv :
    J.toSheafify _ ≫ (J.sheafifyCompIso F P).inv = whiskerRight (J.toSheafify _) _ := by
  rw [Iso.comp_inv_eq]; simp

section

-- We will sheafify `D`-valued presheaves in this section.
variable {FD : D -> D -> Type*} {CD : D -> Type*} [forall X Y, FunLike (FD X Y) (CD X) (CD Y)]
variable [ConcreteCategory D FD] [PreservesLimitsOfSize.{max v u, max v u} (forget D)]
  [forall X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)] [(forget D).ReflectsIsomorphisms]

@[simp]
/--
theorem `sheafifyCompIso_inv_eq_sheafifyLift` / 定理 `sheafifyCompIso_inv_eq_sheafifyLift`

English:
theorem sheafifyCompIso_inv_eq_sheafifyLift
  proof: by
  apply J.sheafifyLift_unique
  rw [Iso.comp_inv_eq]
  simp

中文:
定理 sheafifyCompIso_inv_eq_sheafifyLift
  证明: by
  apply J.sheafifyLift_unique
  rw [Iso.comp_inv_eq]
  simp

Depends on / 依赖: Iso.comp_inv_eq, J.sheafifyLift_unique, comp_inv_eq, sheafifyLift_unique
-/
theorem sheafifyCompIso_inv_eq_sheafifyLift :
    (J.sheafifyCompIso F P).inv =
      J.sheafifyLift (whiskerRight (J.toSheafify P) F)
        (HasSheafCompose.isSheaf _ ((J.sheafify_isSheaf _))) := by
  apply J.sheafifyLift_unique
  rw [Iso.comp_inv_eq]
  simp

end

end CategoryTheory.GrothendieckTopology
