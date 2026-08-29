/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.FullSubcategory

/-!

# Limits and colimits of sheaves

## Limits

We prove that the forgetful functor from `Sheaf J D` to presheaves creates limits.
If the target category `D` has limits (of a certain shape),
this then implies that `Sheaf J D` has limits of the same shape and that the forgetful
functor preserves these limits.

## Colimits

Given a diagram `F : K ⥤ Sheaf J D` of sheaves, and a colimit cocone on the level of presheaves,
we show that the cocone obtained by sheafifying the cocone point is a colimit cocone of sheaves.

This allows us to show that `Sheaf J D` has colimits (of a certain shape) as soon as `D` does.

-/

@[expose] public section


namespace CategoryTheory

namespace Sheaf

open CategoryTheory.Limits

open Opposite

universe w w' v u z z' u₁ u₂

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {D : Type w} [Category.{w'} D]
variable {K : Type z} [Category.{z'} K]

section Limits

noncomputable section

section

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `multiforkEvaluationCone` / `multiforkEvaluationCone` 的定义

English:
definition multiforkEvaluationCone
  signature: (F : K ⥤ Sheaf J D) (E : Cone (F ⋙ sheafToPresheaf J D)) (X : C)
  body: S.pt
  π :=
    { app := fun k => (Presheaf.isLimitOfIsSheaf J (F.obj k).1 W (F.obj k).2).lift <|
        Multifork.ofι _ S.pt (fun i => S.ι i ≫ (E.π.app k).app (op i.Y))
          (by
            intro i
            simp only [Category.assoc]
            erw [← (E.π.app k).naturality, ← (E.π.app k).naturality]
            dsimp
            simp only [← Category.assoc]
            congr 1
            apply S.condition)
      naturality := by
        intro i j f
        dsimp [Presheaf.isLimitOfIsSheaf]
        rw [Category.id_comp]
        apply Presheaf.IsSheaf.hom_ext (F.obj j).2 W
        intro ii
        rw [Presheaf.IsSheaf.amalgamate_map]; rw [Category.assoc]; rw [← (F.map f).hom.naturality]; rw [←
          Category.assoc]; rw [Presheaf.IsSheaf.amalgamate_map]
        erw [Category.assoc, ← E.w f]
        cat_disch }

中文:
定义 multiforkEvaluationCone
  签名: (F : K ⥤ 层 J D) (E : 锥 (F ⋙ sheafToPresheaf J D)) (X : C)
  定义体: S.pt
  π :=
    { app := fun k => (Presheaf.isLimitOfIsSheaf J (F.obj k).1 W (F.obj k).2).lift <|
        Multifork.ofι _ S.pt (fun i => S.ι i ≫ (E.π.app k).app (op i.Y))
          (by
            intro i
            simp only [Category.assoc]
            erw [← (E.π.app k).naturality, ← (E.π.app k).naturality]
            dsimp
            simp only [← Category.assoc]
            congr 1
            apply S.condition)
      naturality := by
        intro i j f
        dsimp [Presheaf.isLimitOfIsSheaf]
        rw [Category.id_comp]
        apply Presheaf.IsSheaf.hom_ext (F.obj j).2 W
        intro ii
        rw [Presheaf.IsSheaf.amalgamate_map]; rw [Category.assoc]; rw [← (F.map f).hom.naturality]; rw [←
          Category.assoc]; rw [Presheaf.IsSheaf.amalgamate_map]
        erw [Category.assoc, ← E.w f]
        cat_disch }

Depends on / 依赖: S.pt
-/
def multiforkEvaluationCone (F : K ⥤ Sheaf J D) (E : Cone (F ⋙ sheafToPresheaf J D)) (X : C)
    (W : J.Cover X) (S : Multifork (W.index E.pt)) :
    Cone (F ⋙ sheafToPresheaf J D ⋙ (evaluation Cᵒᵖ D).obj (op X)) where
  pt := S.pt
  π :=
    { app := fun k => (Presheaf.isLimitOfIsSheaf J (F.obj k).1 W (F.obj k).2).lift <|
        Multifork.ofι _ S.pt (fun i => S.ι i ≫ (E.π.app k).app (op i.Y))
          (by
            intro i
            simp only [Category.assoc]
            erw [← (E.π.app k).naturality, ← (E.π.app k).naturality]
            dsimp
            simp only [← Category.assoc]
            congr 1
            apply S.condition)
      naturality := by
        intro i j f
        dsimp [Presheaf.isLimitOfIsSheaf]
        rw [Category.id_comp]
        apply Presheaf.IsSheaf.hom_ext (F.obj j).2 W
        intro ii
        rw [Presheaf.IsSheaf.amalgamate_map]; rw [Category.assoc]; rw [← (F.map f).hom.naturality]; rw [←
          Category.assoc]; rw [Presheaf.IsSheaf.amalgamate_map]
        erw [Category.assoc, ← E.w f]
        cat_disch }

variable [HasLimitsOfShape K D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimitMultiforkOfIsLimit` / `isLimitMultiforkOfIsLimit` 的定义

English:
definition isLimitMultiforkOfIsLimit
  signature: (F : K ⥤ Sheaf J D) (E : Cone (F ⋙ sheafToPresheaf J D))
  body: Multifork.IsLimit.mk _
    (fun S => (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).lift <|
      multiforkEvaluationCone F E X W S)
    (by
      intro S i
      apply (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op i.Y)) hE).hom_ext
      intro k
      dsimp [Multifork.ofι]
      erw [Category.assoc, (E.π.app k).naturality]
      dsimp
      rw [← Category.assoc]
      erw [(isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).fac
        (multiforkEvaluationCone F E X W S)]
      dsimp [multiforkEvaluationCone, Presheaf.isLimitOfIsSheaf]
      rw [Presheaf.IsSheaf.amalgamate_map])
    (by
      intro S m hm
      apply (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).hom_ext
      intro k
      dsimp
      erw [(isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).fac]
      apply Presheaf.IsSheaf.hom_ext (F.obj k).2 W
      intro i
      dsimp only [multiforkEvaluationCone, Presheaf.isLimitOfIsSheaf]
      rw [(F.obj k).property.amalgamate_map]
      dsimp [Multifork.ofι]
      change _ = S.ι i ≫ _
      erw [← hm, Category.assoc, ← (E.π.app k).naturality, Category.assoc]
      rfl)

中文:
定义 isLimitMultiforkOfIsLimit
  签名: (F : K ⥤ 层 J D) (E : 锥 (F ⋙ sheafToPresheaf J D))
  定义体: Multifork.IsLimit.mk _
    (fun S => (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).lift <|
      multiforkEvaluationCone F E X W S)
    (by
      intro S i
      apply (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op i.Y)) hE).hom_ext
      intro k
      dsimp [Multifork.ofι]
      erw [Category.assoc, (E.π.app k).naturality]
      dsimp
      rw [← Category.assoc]
      erw [(isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).fac
        (multiforkEvaluationCone F E X W S)]
      dsimp [multiforkEvaluationCone, Presheaf.isLimitOfIsSheaf]
      rw [Presheaf.IsSheaf.amalgamate_map])
    (by
      intro S m hm
      apply (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).hom_ext
      intro k
      dsimp
      erw [(isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).fac]
      apply Presheaf.IsSheaf.hom_ext (F.obj k).2 W
      intro i
      dsimp only [multiforkEvaluationCone, Presheaf.isLimitOfIsSheaf]
      rw [(F.obj k).property.amalgamate_map]
      dsimp [Multifork.ofι]
      change _ = S.ι i ≫ _
      erw [← hm, Category.assoc, ← (E.π.app k).naturality, Category.assoc]
      rfl)

Depends on / 依赖: Category, Category.assoc, IsLimit, Multifork, Multifork.IsLimit.mk, Multifork.of, Presheaf, Presheaf.IsShe, Presheaf.isLimitOfIsSheaf, evaluation, hom_ext, isLimitOfIsSheaf, isLimitOfPreserves, multiforkEvaluationCone, naturality
-/
def isLimitMultiforkOfIsLimit (F : K ⥤ Sheaf J D) (E : Cone (F ⋙ sheafToPresheaf J D))
    (hE : IsLimit E) (X : C) (W : J.Cover X) : IsLimit (W.multifork E.pt) :=
  Multifork.IsLimit.mk _
    (fun S => (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).lift <|
      multiforkEvaluationCone F E X W S)
    (by
      intro S i
      apply (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op i.Y)) hE).hom_ext
      intro k
      dsimp [Multifork.ofι]
      erw [Category.assoc, (E.π.app k).naturality]
      dsimp
      rw [← Category.assoc]
      erw [(isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).fac
        (multiforkEvaluationCone F E X W S)]
      dsimp [multiforkEvaluationCone, Presheaf.isLimitOfIsSheaf]
      rw [Presheaf.IsSheaf.amalgamate_map])
    (by
      intro S m hm
      apply (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).hom_ext
      intro k
      dsimp
      erw [(isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).fac]
      apply Presheaf.IsSheaf.hom_ext (F.obj k).2 W
      intro i
      dsimp only [multiforkEvaluationCone, Presheaf.isLimitOfIsSheaf]
      rw [(F.obj k).property.amalgamate_map]
      dsimp [Multifork.ofι]
      change _ = S.ι i ≫ _
      erw [← hm, Category.assoc, ← (E.π.app k).naturality, Category.assoc]
      rfl)

/--
theorem `isSheaf_of_isLimit` / 定理 `isSheaf_of_isLimit`

English:
theorem isSheaf_of_isLimit
  statement: (F : K ⥤ Sheaf J D) (E : Cone (F ⋙ sheafToPresheaf J D))
  proof: by
  rw [Presheaf.isSheaf_iff_multifork]
  intro X S
  exact ⟨isLimitMultiforkOfIsLimit _ _ hE _ _⟩

中文:
定理 isSheaf_of_isLimit
  结论: (F : K ⥤ 层 J D) (E : 锥 (F ⋙ sheafToPresheaf J D))
  证明: by
  rw [Presheaf.isSheaf_iff_multifork]
  intro X S
  exact ⟨isLimitMultiforkOfIsLimit _ _ hE _ _⟩

Depends on / 依赖: Presheaf, Presheaf.isSheaf_iff_multifork, isLimitMultiforkOfIsLimit, isSheaf_iff_multifork
-/
theorem isSheaf_of_isLimit (F : K ⥤ Sheaf J D) (E : Cone (F ⋙ sheafToPresheaf J D))
    (hE : IsLimit E) : Presheaf.IsSheaf J E.pt := by
  rw [Presheaf.isSheaf_iff_multifork]
  intro X S
  exact ⟨isLimitMultiforkOfIsLimit _ _ hE _ _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ObjectProperty.IsClosedUnderLimitsOfShape (Presheaf.IsSheaf J (A := D)) K
  body: by
    rintro P ⟨h⟩
    let F : K ⥤ Sheaf J D := ObjectProperty.lift _ h.diag h.prop_diag_obj
    exact isSheaf_of_isLimit F _ h.isLimit

中文:
实例 :
  签名: ObjectProperty.是ClosedUnderLimitsOfShape (预层.是层 J (A := D)) K
  定义体: by
    rintro P ⟨h⟩
    let F : K ⥤ Sheaf J D := ObjectProperty.lift _ h.diag h.prop_diag_obj
    exact isSheaf_of_isLimit F _ h.isLimit
-/
instance : ObjectProperty.IsClosedUnderLimitsOfShape (Presheaf.IsSheaf J (A := D)) K where
  limitsOfShape_le := by
    rintro P ⟨h⟩
    let F : K ⥤ Sheaf J D := ObjectProperty.lift _ h.diag h.prop_diag_obj
    exact isSheaf_of_isLimit F _ h.isLimit

/--
Instance `createsLimitsOfShape` / 实例 `createsLimitsOfShape`

English:
instance createsLimitsOfShape
  signature: : CreatesLimitsOfShape K (sheafToPresheaf J D) where

中文:
实例 createsLimitsOfShape
  签名: : 创造形状极限 K (sheafToPresheaf J D) where
-/
instance createsLimitsOfShape : CreatesLimitsOfShape K (sheafToPresheaf J D) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLimitsOfShape K (Sheaf J D)
  body: hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf J D)

中文:
实例 :
  签名: 有形状极限 K (层 J D)
  定义体: hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf J D)

Depends on / 依赖: hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape, sheafToPresheaf
-/
instance : HasLimitsOfShape K (Sheaf J D) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf J D)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteProducts
  signature: D] : HasFiniteProducts (Sheaf J D)
  body: ⟨inferInstance⟩

中文:
实例 [有FiniteProducts
  签名: D] : 有FiniteProducts (层 J D)
  定义体: ⟨inferInstance⟩
-/
instance [HasFiniteProducts D] : HasFiniteProducts (Sheaf J D) :=
  ⟨inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteLimits
  signature: D] : HasFiniteLimits (Sheaf J D)
  body: ⟨fun _ => inferInstance⟩

中文:
实例 [有有限极限
  签名: D] : 有有限极限 (层 J D)
  定义体: ⟨fun _ => inferInstance⟩
-/
instance [HasFiniteLimits D] : HasFiniteLimits (Sheaf J D) :=
  ⟨fun _ => inferInstance⟩

end

/--
Instance `createsLimits` / 实例 `createsLimits`

English:
instance createsLimits
  signature: [HasLimitsOfSize.{u₁, u₂} D]
  body: ⟨createsLimitsOfShape⟩

中文:
实例 createsLimits
  签名: [有LimitsOfSize.{u₁, u₂} D]
  定义体: ⟨createsLimitsOfShape⟩

Depends on / 依赖: createsLimitsOfShape
-/
instance createsLimits [HasLimitsOfSize.{u₁, u₂} D] :
    CreatesLimitsOfSize.{u₁, u₂} (sheafToPresheaf J D) :=
  ⟨createsLimitsOfShape⟩

/--
Instance `hasLimitsOfSize` / 实例 `hasLimitsOfSize`

English:
instance hasLimitsOfSize
  signature: [HasLimitsOfSize.{u₁, u₂} D]
  body: hasLimits_of_hasLimits_createsLimits (sheafToPresheaf J D)

中文:
实例 hasLimitsOfSize
  签名: [有LimitsOfSize.{u₁, u₂} D]
  定义体: hasLimits_of_hasLimits_createsLimits (sheafToPresheaf J D)

Depends on / 依赖: hasLimits_of_hasLimits_createsLimits, sheafToPresheaf
-/
instance hasLimitsOfSize [HasLimitsOfSize.{u₁, u₂} D] : HasLimitsOfSize.{u₁, u₂} (Sheaf J D) :=
  hasLimits_of_hasLimits_createsLimits (sheafToPresheaf J D)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteLimits
  signature: D] :
  body: inferInstance

example {D : Type w} [Category.{max v u} D] [HasLimits D] :
    HasLimits (Sheaf J D) := inferInstance

中文:
实例 [有有限极限
  签名: D] :
  定义体: inferInstance

example {D : Type w} [Category.{max v u} D] [HasLimits D] :
    HasLimits (Sheaf J D) := inferInstance
-/
instance [HasFiniteLimits D] :
    PreservesFiniteLimits (sheafToPresheaf J D) where
  preservesFiniteLimits _ _ _ := inferInstance

example {D : Type w} [Category.{max v u} D] [HasLimits D] :
    HasLimits (Sheaf J D) := inferInstance

end

end Limits

section Colimits

variable [HasWeakSheafify J D]

/--
Definition of `sheafifyCocone` / `sheafifyCocone` 的定义

English:
definition sheafifyCocone
  signature: {F : K ⥤ Sheaf J D}
  body: (Cocone.precompose
    (Functor.isoWhiskerLeft F (asIso (sheafificationAdjunction J D).counit).symm).hom).obj
    ((presheafToSheaf J D).mapCocone E)

中文:
定义 sheafifyCocone
  签名: {F : K ⥤ 层 J D}
  定义体: (Cocone.precompose
    (Functor.isoWhiskerLeft F (asIso (sheafificationAdjunction J D).counit).symm).hom).obj
    ((presheafToSheaf J D).mapCocone E)

Depends on / 依赖: Cocone, Cocone.precompose, Functor, Functor.isoWhiskerLeft, counit, isoWhiskerLeft, mapCocone, precompose, presheafToSheaf, sheafificationAdjunction
-/
noncomputable def sheafifyCocone {F : K ⥤ Sheaf J D}
    (E : Cocone (F ⋙ sheafToPresheaf J D)) : Cocone F :=
  (Cocone.precompose
    (Functor.isoWhiskerLeft F (asIso (sheafificationAdjunction J D).counit).symm).hom).obj
    ((presheafToSheaf J D).mapCocone E)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `sheafifyCocone_ι_app_val` / 引理 `sheafifyCocone_ι_app_val`

English:
lemma sheafifyCocone_ι_app_val
  proof: by
  rw [← cancel_epi ((sheafToPresheaf _ _).map
    ((sheafificationAdjunction J D).counit.app (F.obj k)))]
  dsimp [sheafifyCocone]
  rw [← ObjectProperty.FullSubcategory.comp_hom_assoc]; rw [← NatTrans.comp_app]; rw [IsIso.hom_inv_id]; rw [NatTrans.id_app]
  dsimp
  rw [Category.id_comp]; rw [toSheafify_naturality]; rw [sheafificationAdjunction_counit_app_val]; rw [sheafifyLift_id_toSheafify_assoc]

中文:
引理 sheafifyCocone_ι_app_val
  证明: by
  rw [← cancel_epi ((sheafToPresheaf _ _).map
    ((sheafificationAdjunction J D).counit.app (F.obj k)))]
  dsimp [sheafifyCocone]
  rw [← ObjectProperty.FullSubcategory.comp_hom_assoc]; rw [← NatTrans.comp_app]; rw [IsIso.hom_inv_id]; rw [NatTrans.id_app]
  dsimp
  rw [Category.id_comp]; rw [toSheafify_naturality]; rw [sheafificationAdjunction_counit_app_val]; rw [sheafifyLift_id_toSheafify_assoc]

Depends on / 依赖: Category, Category.id_comp, F.obj, FullSubcategory, IsIso.hom_inv_id, NatTrans, NatTrans.comp_app, NatTrans.id_app, ObjectProperty, ObjectProperty.FullSubcategory.comp_hom_assoc, cancel_epi, comp_app, comp_hom_assoc, counit, counit.app, hom_inv_id, id_app, id_comp, sheafToPresheaf, sheafificationAdjunction
-/
lemma sheafifyCocone_ι_app_val
    {F : K ⥤ Sheaf J D} (E : Cocone (F ⋙ sheafToPresheaf J D)) (k : K) :
    ((Sheaf.sheafifyCocone E).ι.app k).hom =
      E.ι.app k ≫ CategoryTheory.toSheafify J E.pt := by
  rw [← cancel_epi ((sheafToPresheaf _ _).map
    ((sheafificationAdjunction J D).counit.app (F.obj k)))]
  dsimp [sheafifyCocone]
  rw [← ObjectProperty.FullSubcategory.comp_hom_assoc]; rw [← NatTrans.comp_app]; rw [IsIso.hom_inv_id]; rw [NatTrans.id_app]
  dsimp
  rw [Category.id_comp]; rw [toSheafify_naturality]; rw [sheafificationAdjunction_counit_app_val]; rw [sheafifyLift_id_toSheafify_assoc]

/--
Definition of `isColimitSheafifyCocone` / `isColimitSheafifyCocone` 的定义

English:
definition isColimitSheafifyCocone
  signature: {F : K ⥤ Sheaf J D}
  body: (IsColimit.precomposeHomEquiv _ ((presheafToSheaf J D).mapCocone E)).symm
    (isColimitOfPreserves _ hE)

中文:
定义 isColimitSheafifyCocone
  签名: {F : K ⥤ 层 J D}
  定义体: (IsColimit.precomposeHomEquiv _ ((presheafToSheaf J D).mapCocone E)).symm
    (isColimitOfPreserves _ hE)

Depends on / 依赖: IsColimit, IsColimit.precomposeHomEquiv, isColimitOfPreserves, mapCocone, precomposeHomEquiv, presheafToSheaf
-/
noncomputable def isColimitSheafifyCocone {F : K ⥤ Sheaf J D}
    (E : Cocone (F ⋙ sheafToPresheaf J D)) (hE : IsColimit E) : IsColimit (sheafifyCocone E) :=
  (IsColimit.precomposeHomEquiv _ ((presheafToSheaf J D).mapCocone E)).symm
    (isColimitOfPreserves _ hE)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimitsOfShape
  signature: K D] : HasColimitsOfShape K (Sheaf J D)
  body: ⟨fun _ => HasColimit.mk
    ⟨sheafifyCocone (colimit.cocone _), isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩

中文:
实例 [有形状余极限
  签名: K D] : 有形状余极限 K (层 J D)
  定义体: ⟨fun _ => HasColimit.mk
    ⟨sheafifyCocone (colimit.cocone _), isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩

Depends on / 依赖: HasColimit, HasColimit.mk, cocone, colimit, colimit.cocone, colimit.isColimit, isColimit, isColimitSheafifyCocone, sheafifyCocone
-/
instance [HasColimitsOfShape K D] : HasColimitsOfShape K (Sheaf J D) :=
  ⟨fun _ => HasColimit.mk
    ⟨sheafifyCocone (colimit.cocone _), isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteCoproducts
  signature: D] : HasFiniteCoproducts (Sheaf J D)
  body: ⟨inferInstance⟩

中文:
实例 [有FiniteCoproducts
  签名: D] : 有FiniteCoproducts (层 J D)
  定义体: ⟨inferInstance⟩
-/
instance [HasFiniteCoproducts D] : HasFiniteCoproducts (Sheaf J D) :=
  ⟨inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteColimits
  signature: D] : HasFiniteColimits (Sheaf J D)
  body: ⟨fun _ => inferInstance⟩

中文:
实例 [有有限余极限
  签名: D] : 有有限余极限 (层 J D)
  定义体: ⟨fun _ => inferInstance⟩
-/
instance [HasFiniteColimits D] : HasFiniteColimits (Sheaf J D) :=
  ⟨fun _ => inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimitsOfSize.{u₁,
  signature: u₂} D] : HasColimitsOfSize.{u₁, u₂} (Sheaf J D)
  body: ⟨inferInstance⟩

中文:
实例 [有余limitsOfSize.{u₁,
  签名: u₂} D] : 有余limitsOfSize.{u₁, u₂} (层 J D)
  定义体: ⟨inferInstance⟩
-/
instance [HasColimitsOfSize.{u₁, u₂} D] : HasColimitsOfSize.{u₁, u₂} (Sheaf J D) :=
  ⟨inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/--
If every cocone on a diagram of sheaves which is a colimit on the level of presheaves satisfies
the condition that the cocone point is a sheaf, then the functor from sheaves to presheaves
creates colimits of the diagram.
Note: this almost never holds in sheaf categories in general, but it does for the extensive
topology (see `Mathlib/CategoryTheory/Sites/Coherent/ExtensiveColimits.lean`).
-/
@[instance_reducible]
/--
Definition of `createsColimitOfIsSheaf` / `createsColimitOfIsSheaf` 的定义

English:
definition createsColimitOfIsSheaf
  signature: (F : K ⥤ Sheaf J D)
  body: createsColimitOfReflectsIso fun E hE =>
    { liftedCocone := ⟨⟨E.pt, h _ hE⟩,
⟨fun _ => ⟨E.ι.app _⟩, fun _ _ _ => Sheaf.hom_ext E.ι.naturality _⟩⟩
      validLift := Cocone.ext (eqToIso rfl) fun j => by simp
      makesColimit :=
        { desc := fun S => ⟨hE.desc ((sheafToPresheaf J D).mapCocone S)⟩
          fac := fun S j => by ext1; dsimp; rw [hE.fac]; rfl
          uniq := fun S m hm => by
            ext1
            exact hE.uniq ((sheafToPresheaf J D).mapCocone S) m.hom fun j =>
              (ObjectProperty.ι _).congr_map (hm j) } }

中文:
定义 createsColimitOfIsSheaf
  签名: (F : K ⥤ 层 J D)
  定义体: createsColimitOfReflectsIso fun E hE =>
    { liftedCocone := ⟨⟨E.pt, h _ hE⟩,
⟨fun _ => ⟨E.ι.app _⟩, fun _ _ _ => Sheaf.hom_ext E.ι.naturality _⟩⟩
      validLift := Cocone.ext (eqToIso rfl) fun j => by simp
      makesColimit :=
        { desc := fun S => ⟨hE.desc ((sheafToPresheaf J D).mapCocone S)⟩
          fac := fun S j => by ext1; dsimp; rw [hE.fac]; rfl
          uniq := fun S m hm => by
            ext1
            exact hE.uniq ((sheafToPresheaf J D).mapCocone S) m.hom fun j =>
              (ObjectProperty.ι _).congr_map (hm j) } }

Depends on / 依赖: Cocone, Cocone.ext, E.pt, ObjectProperty, Sheaf.hom_ext, congr_map, createsColimitOfReflectsIso, eqToIso, hE.desc, hE.fac, hE.uniq, hom_ext, liftedCocone, m.hom, makesColimit, mapCocone, naturality, sheafToPresheaf, validLift
-/
def createsColimitOfIsSheaf (F : K ⥤ Sheaf J D)
    (h : forall (c : Cocone (F ⋙ sheafToPresheaf J D)) (_ : IsColimit c), Presheaf.IsSheaf J c.pt) :
    CreatesColimit F (sheafToPresheaf J D) :=
  createsColimitOfReflectsIso fun E hE =>
    { liftedCocone := ⟨⟨E.pt, h _ hE⟩,
⟨fun _ => ⟨E.ι.app _⟩, fun _ _ _ => Sheaf.hom_ext E.ι.naturality _⟩⟩
      validLift := Cocone.ext (eqToIso rfl) fun j => by simp
      makesColimit :=
        { desc := fun S => ⟨hE.desc ((sheafToPresheaf J D).mapCocone S)⟩
          fac := fun S j => by ext1; dsimp; rw [hE.fac]; rfl
          uniq := fun S m hm => by
            ext1
            exact hE.uniq ((sheafToPresheaf J D).mapCocone S) m.hom fun j =>
              (ObjectProperty.ι _).congr_map (hm j) } }

variable {D : Type w} [Category.{max v u} D]

example [HasLimits D] : HasLimits (Sheaf J D) := inferInstance

end Colimits

end Sheaf

end CategoryTheory
