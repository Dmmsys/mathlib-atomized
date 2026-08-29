/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# An exact functor induces a functor on derived categories

In this file, we show that if `F : C₁ ⥤ C₂` is an exact functor between
abelian categories, then there is an induced triangulated functor
`F.mapDerivedCategory : DerivedCategory C₁ ⥤ DerivedCategory C₂`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory Category Limits

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

namespace CategoryTheory.Functor

/--
Definition of `mapDerivedCategory` / `mapDerivedCategory` 的定义

English:
definition mapDerivedCategory
  signature: : DerivedCategory C₁ ⥤ DerivedCategory C₂
  body: F.mapHomologicalComplexUpToQuasiIso (ComplexShape.up Int)

中文:
定义 mapDerivedCategory
  签名: : 导出范畴 C₁ ⥤ 导出范畴 C₂
  定义体: F.mapHomologicalComplexUpToQuasiIso (ComplexShape.up Int)

Depends on / 依赖: ComplexShape, ComplexShape.up, F.mapHomologicalComplexUpToQuasiIso, mapHomologicalComplexUpToQuasiIso
-/
noncomputable def mapDerivedCategory : DerivedCategory C₁ ⥤ DerivedCategory C₂ :=
  F.mapHomologicalComplexUpToQuasiIso (ComplexShape.up Int)

/--
Definition of `mapDerivedCategoryFactors` / `mapDerivedCategoryFactors` 的定义

English:
definition mapDerivedCategoryFactors
  signature: :
  body: F.mapHomologicalComplexUpToQuasiIsoFactors _

@[reassoc]

中文:
定义 mapDerivedCategoryFactors
  签名: :
  定义体: F.mapHomologicalComplexUpToQuasiIsoFactors _

@[reassoc]

Depends on / 依赖: F.mapHomologicalComplexUpToQuasiIsoFactors, mapHomologicalComplexUpToQuasiIsoFactors
-/
noncomputable def mapDerivedCategoryFactors :
    DerivedCategory.Q ⋙ F.mapDerivedCategory ≅
      F.mapHomologicalComplex (ComplexShape.up Int) ⋙ DerivedCategory.Q :=
  F.mapHomologicalComplexUpToQuasiIsoFactors _

@[reassoc]
/--
lemma `mapDerivedCategoryFactors_hom_naturality` / 引理 `mapDerivedCategoryFactors_hom_naturality`

English:
lemma mapDerivedCategoryFactors_hom_naturality
  given: {X Y : CochainComplex C₁ Int} (f : X ⟶ Y)
  proof: F.mapDerivedCategoryFactors.hom.naturality f

中文:
引理 mapDerivedCategoryFactors_hom_naturality
  条件: {X Y : 上链复形 C₁ 整数} (f : X ⟶ Y)
  证明: F.mapDerivedCategoryFactors.hom.naturality f

Depends on / 依赖: F.mapDerivedCategoryFactors.hom.naturality, mapDerivedCategoryFactors, naturality
-/
lemma mapDerivedCategoryFactors_hom_naturality {X Y : CochainComplex C₁ Int} (f : X ⟶ Y) :
    F.mapDerivedCategory.map (DerivedCategory.Q.map f) ≫ F.mapDerivedCategoryFactors.hom.app Y =
      F.mapDerivedCategoryFactors.hom.app X ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up Int)).map f) :=
  F.mapDerivedCategoryFactors.hom.naturality f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: ⟨F.mapDerivedCategoryFactors⟩

中文:
实例 :
  定义体: ⟨F.mapDerivedCategoryFactors⟩

Depends on / 依赖: F.mapDerivedCategoryFactors, mapDerivedCategoryFactors
-/
noncomputable instance :
    Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up Int))
      (F.mapHomologicalComplex _ ⋙ DerivedCategory.Q) F.mapDerivedCategory :=
  ⟨F.mapDerivedCategoryFactors⟩

/--
Definition of `mapDerivedCategoryFactorsh` / `mapDerivedCategoryFactorsh` 的定义

English:
definition mapDerivedCategoryFactorsh
  signature: :
  body: F.mapHomologicalComplexUpToQuasiIsoFactorsh _

中文:
定义 mapDerivedCategoryFactorsh
  签名: :
  定义体: F.mapHomologicalComplexUpToQuasiIsoFactorsh _

Depends on / 依赖: F.mapHomologicalComplexUpToQuasiIsoFactorsh, mapHomologicalComplexUpToQuasiIsoFactorsh
-/
noncomputable def mapDerivedCategoryFactorsh :
    DerivedCategory.Qh ⋙ F.mapDerivedCategory ≅
      F.mapHomotopyCategory (ComplexShape.up Int) ⋙ DerivedCategory.Qh :=
  F.mapHomologicalComplexUpToQuasiIsoFactorsh _

/--
lemma `mapDerivedCategoryFactorsh_hom_app` / 引理 `mapDerivedCategoryFactorsh_hom_app`

English:
lemma mapDerivedCategoryFactorsh_hom_app
  given: (K : CochainComplex C₁ Int)
  proof: F.mapHomologicalComplexUpToQuasiIsoFactorsh_hom_app K

中文:
引理 mapDerivedCategoryFactorsh_hom_app
  条件: (K : 上链复形 C₁ 整数)
  证明: F.mapHomologicalComplexUpToQuasiIsoFactorsh_hom_app K

Depends on / 依赖: F.mapHomologicalComplexUpToQuasiIsoFactorsh_hom_app, mapHomologicalComplexUpToQuasiIsoFactorsh_hom_app
-/
lemma mapDerivedCategoryFactorsh_hom_app (K : CochainComplex C₁ Int) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj K) =
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C₁).hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app K ≫
        (DerivedCategory.quotientCompQhIso C₂).inv.app _ ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (ComplexShape.up Int)).inv.app K) :=
  F.mapHomologicalComplexUpToQuasiIsoFactorsh_hom_app K

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: ⟨F.mapDerivedCategoryFactorsh⟩

中文:
实例 :
  定义体: ⟨F.mapDerivedCategoryFactorsh⟩

Depends on / 依赖: F.mapDerivedCategoryFactorsh, mapDerivedCategoryFactorsh
-/
noncomputable instance :
    Localization.Lifting DerivedCategory.Qh
      (HomotopyCategory.quasiIso C₁ (ComplexShape.up Int))
      (F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh) F.mapDerivedCategory :=
  ⟨F.mapDerivedCategoryFactorsh⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: F.mapDerivedCategory.CommShift Int
  body: Functor.commShiftOfLocalization DerivedCategory.Qh
    (HomotopyCategory.quasiIso C₁ (ComplexShape.up Int)) Int
    (F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh)
    F.mapDerivedCategory

中文:
实例 :
  签名: F.mapDerivedCategory.交换Shift 整数
  定义体: Functor.commShiftOfLocalization DerivedCategory.Qh
    (HomotopyCategory.quasiIso C₁ (ComplexShape.up Int)) Int
    (F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh)
    F.mapDerivedCategory

Depends on / 依赖: ComplexShape, ComplexShape.up, DerivedCategory, DerivedCategory.Qh, F.mapDerivedCategory, F.mapHomotopyCategory, Functor, Functor.commShiftOfLocalization, HomotopyCategory, HomotopyCategory.quasiIso, commShiftOfLocalization, mapDerivedCategory, mapHomotopyCategory, quasiIso
-/
noncomputable instance : F.mapDerivedCategory.CommShift Int :=
  Functor.commShiftOfLocalization DerivedCategory.Qh
    (HomotopyCategory.quasiIso C₁ (ComplexShape.up Int)) Int
    (F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh)
    F.mapDerivedCategory

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatTrans.CommShift F.mapDerivedCategoryFactorsh.hom Int
  body: inferInstanceAs (NatTrans.CommShift (Localization.Lifting.iso
      DerivedCategory.Qh (HomotopyCategory.quasiIso C₁ (ComplexShape.up Int))
        (F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh)
          F.mapDerivedCategory).hom Int)

中文:
实例 :
  签名: 自然变换.交换Shift F.mapDerivedCategoryFactorsh.hom 整数
  定义体: inferInstanceAs (NatTrans.CommShift (Localization.Lifting.iso
      DerivedCategory.Qh (HomotopyCategory.quasiIso C₁ (ComplexShape.up Int))
        (F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh)
          F.mapDerivedCategory).hom Int)

Depends on / 依赖: CommShift, ComplexShape, ComplexShape.up, DerivedCategory, DerivedCategory.Qh, F.mapDerivedCategory, F.mapHomotopyCategory, HomotopyCategory, HomotopyCategory.quasiIso, Lifting, Localization, Localization.Lifting.iso, NatTrans, NatTrans.CommShift, mapDerivedCategory, mapHomotopyCategory, quasiIso
-/
instance : NatTrans.CommShift F.mapDerivedCategoryFactorsh.hom Int :=
  inferInstanceAs (NatTrans.CommShift (Localization.Lifting.iso
      DerivedCategory.Qh (HomotopyCategory.quasiIso C₁ (ComplexShape.up Int))
        (F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh)
          F.mapDerivedCategory).hom Int)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatTrans.CommShift F.mapDerivedCategoryFactors.hom Int
  body: NatTrans.CommShift.verticalComposition (DerivedCategory.quotientCompQhIso C₁).inv
    (DerivedCategory.quotientCompQhIso C₂).hom
    (F.mapHomotopyCategoryFactors (ComplexShape.up Int)).hom
    F.mapDerivedCategoryFactorsh.hom F.mapDerivedCategoryFactors.hom Int (by
      ext K
      dsimp
      simp only [id_comp, mapDerivedCategoryFactorsh_hom_app, assoc, comp_id,
        ← Functor.map_comp_assoc, Iso.inv_hom_id_app, map_id, comp_obj])

中文:
实例 :
  签名: 自然变换.交换Shift F.mapDerivedCategoryFactors.hom 整数
  定义体: NatTrans.CommShift.verticalComposition (DerivedCategory.quotientCompQhIso C₁).inv
    (DerivedCategory.quotientCompQhIso C₂).hom
    (F.mapHomotopyCategoryFactors (ComplexShape.up Int)).hom
    F.mapDerivedCategoryFactorsh.hom F.mapDerivedCategoryFactors.hom Int (by
      ext K
      dsimp
      simp only [id_comp, mapDerivedCategoryFactorsh_hom_app, assoc, comp_id,
        ← Functor.map_comp_assoc, Iso.inv_hom_id_app, map_id, comp_obj])

Depends on / 依赖: CommShift, ComplexShape, ComplexShape.up, DerivedCategory, DerivedCategory.quotientCompQhIso, F.mapDerivedCategoryFactors.hom, F.mapDerivedCategoryFactorsh.hom, F.mapHomotopyCategoryFactors, Functor, Functor.map_comp_assoc, Iso.inv_hom_id_app, NatTrans, NatTrans.CommShift.verticalComposition, comp_id, comp_obj, id_comp, inv_hom_id_app, mapDerivedCategoryFactors, mapDerivedCategoryFactorsh, mapDerivedCategoryFactorsh_hom_app
-/
instance : NatTrans.CommShift F.mapDerivedCategoryFactors.hom Int :=
  NatTrans.CommShift.verticalComposition (DerivedCategory.quotientCompQhIso C₁).inv
    (DerivedCategory.quotientCompQhIso C₂).hom
    (F.mapHomotopyCategoryFactors (ComplexShape.up Int)).hom
    F.mapDerivedCategoryFactorsh.hom F.mapDerivedCategoryFactors.hom Int (by
      ext K
      dsimp
      simp only [id_comp, mapDerivedCategoryFactorsh_hom_app, assoc, comp_id,
        ← Functor.map_comp_assoc, Iso.inv_hom_id_app, map_id, comp_obj])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: F.mapDerivedCategory.IsTriangulated
  body: Functor.isTriangulated_of_precomp_iso F.mapDerivedCategoryFactorsh

中文:
实例 :
  签名: F.mapDerivedCategory.是三角
  定义体: Functor.isTriangulated_of_precomp_iso F.mapDerivedCategoryFactorsh

Depends on / 依赖: F.mapDerivedCategoryFactorsh, Functor, Functor.isTriangulated_of_precomp_iso, isTriangulated_of_precomp_iso, mapDerivedCategoryFactorsh
-/
instance : F.mapDerivedCategory.IsTriangulated :=
  Functor.isTriangulated_of_precomp_iso F.mapDerivedCategoryFactorsh

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
  body: inferInstanceAs ((F.mapHomologicalComplex (ComplexShape.up Int)).CommShift Int)

中文:
实例 :
  签名: (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
  定义体: inferInstanceAs ((F.mapHomologicalComplex (ComplexShape.up Int)).CommShift Int)

Depends on / 依赖: CommShift, ComplexShape, ComplexShape.up, F.mapHomologicalComplex, mapHomologicalComplex
-/
instance : (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up Int)).functor.CommShift Int :=
  inferInstanceAs ((F.mapHomologicalComplex (ComplexShape.up Int)).CommShift Int)

/--
Definition of `mapDerivedCategorySingleFunctor` / `mapDerivedCategorySingleFunctor` 的定义

English:
definition mapDerivedCategorySingleFunctor
  signature: (n : Int)
  body: isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ C₁ n) _ ≪≫
    associator .. ≪≫ isoWhiskerLeft _ F.mapDerivedCategoryFactors ≪≫ (associator ..).symm ≪≫
      isoWhiskerRight (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up Int) n) _ ≪≫
        associator .. ≪≫ (isoWhiskerLeft _ (DerivedCategory.singleFunctorIsoCompQ C₂ n)).symm

中文:
定义 mapDerivedCategorySingleFunctor
  签名: (n : 整数)
  定义体: isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ C₁ n) _ ≪≫
    associator .. ≪≫ isoWhiskerLeft _ F.mapDerivedCategoryFactors ≪≫ (associator ..).symm ≪≫
      isoWhiskerRight (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up Int) n) _ ≪≫
        associator .. ≪≫ (isoWhiskerLeft _ (DerivedCategory.singleFunctorIsoCompQ C₂ n)).symm

Depends on / 依赖: ComplexShape, ComplexShape.up, DerivedCategory, DerivedCategory.singleFunctorIsoCompQ, F.mapDerivedCategoryFactors, HomologicalComplex, HomologicalComplex.singleMapHomologicalComplex, associator, isoWhiskerLeft, isoWhiskerRight, mapDerivedCategoryFactors, singleFunctorIsoCompQ, singleMapHomologicalComplex
-/
noncomputable def mapDerivedCategorySingleFunctor (n : Int) :
    DerivedCategory.singleFunctor C₁ n ⋙ F.mapDerivedCategory ≅
      F ⋙ DerivedCategory.singleFunctor C₂ n :=
  isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ C₁ n) _ ≪≫
    associator .. ≪≫ isoWhiskerLeft _ F.mapDerivedCategoryFactors ≪≫ (associator ..).symm ≪≫
      isoWhiskerRight (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up Int) n) _ ≪≫
        associator .. ≪≫ (isoWhiskerLeft _ (DerivedCategory.singleFunctorIsoCompQ C₂ n)).symm

variable (R : Type*) [Ring R] [CategoryTheory.Linear R C₁] [CategoryTheory.Linear R C₂]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Linear
  signature: R] : F.mapDerivedCategory.Linear R
  body: by
  rw [← Localization.functor_linear_iff DerivedCategory.Qh (HomotopyCategory.quasiIso C₁
    (ComplexShape.up Int)) R ((F.mapHomotopyCategory (ComplexShape.up Int)).comp DerivedCategory.Qh)]
  infer_instance

中文:
实例 [F.线性
  签名: R] : F.mapDerivedCategory.线性 R
  定义体: by
  rw [← Localization.functor_linear_iff DerivedCategory.Qh (HomotopyCategory.quasiIso C₁
    (ComplexShape.up Int)) R ((F.mapHomotopyCategory (ComplexShape.up Int)).comp DerivedCategory.Qh)]
  infer_instance

Depends on / 依赖: ComplexShape, ComplexShape.up, DerivedCategory, DerivedCategory.Qh, F.mapHomotopyCategory, HomotopyCategory, HomotopyCategory.quasiIso, Localization, Localization.functor_linear_iff, functor_linear_iff, infer_instance, mapHomotopyCategory, quasiIso
-/
instance [F.Linear R] : F.mapDerivedCategory.Linear R := by
  rw [← Localization.functor_linear_iff DerivedCategory.Qh (HomotopyCategory.quasiIso C₁
    (ComplexShape.up Int)) R ((F.mapHomotopyCategory (ComplexShape.up Int)).comp DerivedCategory.Qh)]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app` / 引理 `mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app`

English:
lemma mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app
  given: (X : C₁)
  proof: by
  simp [Functor.mapDerivedCategorySingleFunctor, Functor.mapCochainComplexSingleFunctor,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    DerivedCategory.singleFunctorIsoCompQ]

中文:
引理 mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app
  条件: (X : C₁)
  证明: by
  simp [Functor.mapDerivedCategorySingleFunctor, Functor.mapCochainComplexSingleFunctor,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    DerivedCategory.singleFunctorIsoCompQ]

Depends on / 依赖: CochainComplex, CochainComplex.singleFunctor, CochainComplex.singleFunctors, DerivedCategory, DerivedCategory.singleFunctorIsoCompQ, Functor, Functor.mapCochainComplexSingleFunctor, Functor.mapDerivedCategorySingleFunctor, mapCochainComplexSingleFunctor, mapDerivedCategorySingleFunctor, singleFunctor, singleFunctorIsoCompQ, singleFunctors
-/
lemma mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app (X : C₁) :
    dsimp% F.mapDerivedCategoryFactors.inv.app ((HomologicalComplex.single C₁ (.up Int) 0).obj X) ≫
      (F.mapDerivedCategorySingleFunctor 0).hom.app X =
    DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app X) := by
  simp [Functor.mapDerivedCategorySingleFunctor, Functor.mapCochainComplexSingleFunctor,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    DerivedCategory.singleFunctorIsoCompQ]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app` / 引理 `mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app`

English:
lemma mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app
  given: (X : C₁)
  proof: by
  simp [Functor.mapDerivedCategorySingleFunctor, Functor.mapCochainComplexSingleFunctor,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    DerivedCategory.singleFunctorIsoCompQ]

中文:
引理 mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app
  条件: (X : C₁)
  证明: by
  simp [Functor.mapDerivedCategorySingleFunctor, Functor.mapCochainComplexSingleFunctor,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    DerivedCategory.singleFunctorIsoCompQ]

Depends on / 依赖: CochainComplex, CochainComplex.singleFunctor, CochainComplex.singleFunctors, DerivedCategory, DerivedCategory.singleFunctorIsoCompQ, Functor, Functor.mapCochainComplexSingleFunctor, Functor.mapDerivedCategorySingleFunctor, mapCochainComplexSingleFunctor, mapDerivedCategorySingleFunctor, singleFunctor, singleFunctorIsoCompQ, singleFunctors
-/
lemma mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app (X : C₁) :
    dsimp% (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
      F.mapDerivedCategoryFactors.hom.app ((HomologicalComplex.single C₁ (.up Int) 0).obj X) =
    DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app X) := by
  simp [Functor.mapDerivedCategorySingleFunctor, Functor.mapCochainComplexSingleFunctor,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    DerivedCategory.singleFunctorIsoCompQ]

end CategoryTheory.Functor
