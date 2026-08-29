/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape

/-!
# Limits in full subcategories

If a property of objects `P` is closed under taking limits,
then limits in `FullSubcategory P` can be constructed from limits in `C`.
More precisely, the inclusion creates such limits.

-/

@[expose] public section


noncomputable section

universe w' w v v₁ v₂ u u₁ u₂

open CategoryTheory

namespace CategoryTheory

namespace Limits

variable {J : Type w} [Category.{w'} J] {C : Type u} [Category.{v} C] {P : ObjectProperty C}

/-- If a `J`-shaped diagram in `FullSubcategory P` has a limit cone in `C` whose cone point lives
    in the full subcategory, then this defines a limit in the full subcategory. -/
@[instance_reducible]
/--
Definition of `createsLimitFullSubcategoryInclusion'` / `createsLimitFullSubcategoryInclusion'` 的定义

English:
definition createsLimitFullSubcategoryInclusion'
  signature: (F : J ⥤ P.FullSubcategory)
  body: createsLimitOfFullyFaithfulOfIso' hc ⟨_, h⟩ (Iso.refl _)

中文:
定义 createsLimitFullSubcategoryInclusion'
  签名: (F : J ⥤ P.满子范畴)
  定义体: createsLimitOfFullyFaithfulOfIso' hc ⟨_, h⟩ (Iso.refl _)

Depends on / 依赖: Iso.refl, createsLimitOfFullyFaithfulOfIso
-/
def createsLimitFullSubcategoryInclusion' (F : J ⥤ P.FullSubcategory)
    {c : Cone (F ⋙ P.ι)} (hc : IsLimit c) (h : P c.pt) :
    CreatesLimit F P.ι :=
  createsLimitOfFullyFaithfulOfIso' hc ⟨_, h⟩ (Iso.refl _)

/-- If a `J`-shaped diagram in `FullSubcategory P` has a limit in `C` whose cone point lives in the
    full subcategory, then this defines a limit in the full subcategory. -/
@[instance_reducible]
/--
Definition of `createsLimitFullSubcategoryInclusion` / `createsLimitFullSubcategoryInclusion` 的定义

English:
definition createsLimitFullSubcategoryInclusion
  signature: (F : J ⥤ P.FullSubcategory)
  body: createsLimitFullSubcategoryInclusion' F (limit.isLimit _) h

中文:
定义 createsLimitFullSubcategoryInclusion
  签名: (F : J ⥤ P.满子范畴)
  定义体: createsLimitFullSubcategoryInclusion' F (limit.isLimit _) h

Depends on / 依赖: createsLimitFullSubcategoryInclusion, isLimit, limit.isLimit
-/
def createsLimitFullSubcategoryInclusion (F : J ⥤ P.FullSubcategory)
    [HasLimit (F ⋙ P.ι)] (h : P (limit (F ⋙ P.ι))) :
    CreatesLimit F P.ι :=
  createsLimitFullSubcategoryInclusion' F (limit.isLimit _) h

/-- If a `J`-shaped diagram in `FullSubcategory P` has a colimit cocone in `C` whose cocone point
    lives in the full subcategory, then this defines a colimit in the full subcategory. -/
@[instance_reducible]
/--
Definition of `createsColimitFullSubcategoryInclusion'` / `createsColimitFullSubcategoryInclusion'` 的定义

English:
definition createsColimitFullSubcategoryInclusion'
  signature: (F : J ⥤ P.FullSubcategory)
  body: createsColimitOfFullyFaithfulOfIso' hc ⟨_, h⟩ (Iso.refl _)

中文:
定义 createsColimitFullSubcategoryInclusion'
  签名: (F : J ⥤ P.满子范畴)
  定义体: createsColimitOfFullyFaithfulOfIso' hc ⟨_, h⟩ (Iso.refl _)

Depends on / 依赖: Iso.refl, createsColimitOfFullyFaithfulOfIso
-/
def createsColimitFullSubcategoryInclusion' (F : J ⥤ P.FullSubcategory)
    {c : Cocone (F ⋙ P.ι)} (hc : IsColimit c) (h : P c.pt) :
    CreatesColimit F P.ι :=
  createsColimitOfFullyFaithfulOfIso' hc ⟨_, h⟩ (Iso.refl _)

/-- If a `J`-shaped diagram in `FullSubcategory P` has a colimit in `C` whose cocone point lives in
    the full subcategory, then this defines a colimit in the full subcategory. -/
@[instance_reducible]
/--
Definition of `createsColimitFullSubcategoryInclusion` / `createsColimitFullSubcategoryInclusion` 的定义

English:
definition createsColimitFullSubcategoryInclusion
  signature: (F : J ⥤ P.FullSubcategory)
  body: createsColimitFullSubcategoryInclusion' F (colimit.isColimit _) h

中文:
定义 createsColimitFullSubcategoryInclusion
  签名: (F : J ⥤ P.满子范畴)
  定义体: createsColimitFullSubcategoryInclusion' F (colimit.isColimit _) h

Depends on / 依赖: colimit, colimit.isColimit, createsColimitFullSubcategoryInclusion, isColimit
-/
def createsColimitFullSubcategoryInclusion (F : J ⥤ P.FullSubcategory)
    [HasColimit (F ⋙ P.ι)]
    (h : P (colimit (F ⋙ P.ι))) :
    CreatesColimit F P.ι :=
  createsColimitFullSubcategoryInclusion' F (colimit.isColimit _) h

variable (P J)

/-- If `P` is closed under limits of shape `J`, then the inclusion creates such limits. -/
@[instance_reducible]
/--
Definition of `createsLimitFullSubcategoryInclusionOfClosed` / `createsLimitFullSubcategoryInclusionOfClosed` 的定义

English:
definition createsLimitFullSubcategoryInclusionOfClosed
  signature: [P.IsClosedUnderLimitsOfShape J]
  body: createsLimitFullSubcategoryInclusion F (P.prop_limit _ fun j => (F.obj j).property)

中文:
定义 createsLimitFullSubcategoryInclusionOfClosed
  签名: [P.是ClosedUnderLimitsOfShape J]
  定义体: createsLimitFullSubcategoryInclusion F (P.prop_limit _ fun j => (F.obj j).property)

Depends on / 依赖: F.obj, P.prop_limit, createsLimitFullSubcategoryInclusion, prop_limit, property
-/
def createsLimitFullSubcategoryInclusionOfClosed [P.IsClosedUnderLimitsOfShape J]
    (F : J ⥤ P.FullSubcategory) [HasLimit (F ⋙ P.ι)] :
    CreatesLimit F P.ι :=
  createsLimitFullSubcategoryInclusion F (P.prop_limit _ fun j => (F.obj j).property)

/--
Instance `createsLimitsOfShapeFullSubcategoryInclusion` / 实例 `createsLimitsOfShapeFullSubcategoryInclusion`

English:
instance createsLimitsOfShapeFullSubcategoryInclusion
  signature: [P.IsClosedUnderLimitsOfShape J]
  body: @fun F => createsLimitFullSubcategoryInclusionOfClosed J P F

中文:
实例 createsLimitsOfShapeFullSubcategoryInclusion
  签名: [P.是ClosedUnderLimitsOfShape J]
  定义体: @fun F => createsLimitFullSubcategoryInclusionOfClosed J P F

Depends on / 依赖: createsLimitFullSubcategoryInclusionOfClosed
-/
instance createsLimitsOfShapeFullSubcategoryInclusion [P.IsClosedUnderLimitsOfShape J]
    [HasLimitsOfShape J C] : CreatesLimitsOfShape J P.ι where
  CreatesLimit := @fun F => createsLimitFullSubcategoryInclusionOfClosed J P F

/--
theorem `hasLimit_of_closedUnderLimits` / 定理 `hasLimit_of_closedUnderLimits`

English:
theorem hasLimit_of_closedUnderLimits
  statement: [P.IsClosedUnderLimitsOfShape J]
  proof: have : CreatesLimit F P.ι :=
    createsLimitFullSubcategoryInclusionOfClosed J P F
  hasLimit_of_created F P.ι

中文:
定理 hasLimit_of_closedUnderLimits
  结论: [P.是ClosedUnderLimitsOfShape J]
  证明: have : CreatesLimit F P.ι :=
    createsLimitFullSubcategoryInclusionOfClosed J P F
  hasLimit_of_created F P.ι

Depends on / 依赖: CreatesLimit, createsLimitFullSubcategoryInclusionOfClosed, hasLimit_of_created
-/
theorem hasLimit_of_closedUnderLimits [P.IsClosedUnderLimitsOfShape J]
    (F : J ⥤ P.FullSubcategory) [HasLimit (F ⋙ P.ι)] : HasLimit F :=
  have : CreatesLimit F P.ι :=
    createsLimitFullSubcategoryInclusionOfClosed J P F
  hasLimit_of_created F P.ι

/--
Instance `hasLimitsOfShape_of_closedUnderLimits` / 实例 `hasLimitsOfShape_of_closedUnderLimits`

English:
instance hasLimitsOfShape_of_closedUnderLimits
  signature: [P.IsClosedUnderLimitsOfShape J]
  body: { has_limit := fun F => hasLimit_of_closedUnderLimits J P F }

中文:
实例 hasLimitsOfShape_of_closedUnderLimits
  签名: [P.是ClosedUnderLimitsOfShape J]
  定义体: { has_limit := fun F => hasLimit_of_closedUnderLimits J P F }

Depends on / 依赖: hasLimit_of_closedUnderLimits, has_limit
-/
instance hasLimitsOfShape_of_closedUnderLimits [P.IsClosedUnderLimitsOfShape J]
    [HasLimitsOfShape J C] : HasLimitsOfShape J P.FullSubcategory :=
  { has_limit := fun F => hasLimit_of_closedUnderLimits J P F }

/-- If `P` is closed under colimits of shape `J`, then the inclusion creates such colimits. -/
@[instance_reducible]
/--
Definition of `createsColimitFullSubcategoryInclusionOfClosed` / `createsColimitFullSubcategoryInclusionOfClosed` 的定义

English:
definition createsColimitFullSubcategoryInclusionOfClosed
  signature: [P.IsClosedUnderColimitsOfShape J]
  body: createsColimitFullSubcategoryInclusion F (P.prop_colimit _ fun j => (F.obj j).property)

中文:
定义 createsColimitFullSubcategoryInclusionOfClosed
  签名: [P.是ClosedUnderColimitsOfShape J]
  定义体: createsColimitFullSubcategoryInclusion F (P.prop_colimit _ fun j => (F.obj j).property)

Depends on / 依赖: F.obj, P.prop_colimit, createsColimitFullSubcategoryInclusion, prop_colimit, property
-/
def createsColimitFullSubcategoryInclusionOfClosed [P.IsClosedUnderColimitsOfShape J]
    (F : J ⥤ P.FullSubcategory) [HasColimit (F ⋙ P.ι)] :
    CreatesColimit F P.ι :=
  createsColimitFullSubcategoryInclusion F (P.prop_colimit _ fun j => (F.obj j).property)

/--
Instance `createsColimitsOfShapeFullSubcategoryInclusion` / 实例 `createsColimitsOfShapeFullSubcategoryInclusion`

English:
instance createsColimitsOfShapeFullSubcategoryInclusion
  signature: [P.IsClosedUnderColimitsOfShape J]
  body: @fun F => createsColimitFullSubcategoryInclusionOfClosed J P F

中文:
实例 createsColimitsOfShapeFullSubcategoryInclusion
  签名: [P.是ClosedUnderColimitsOfShape J]
  定义体: @fun F => createsColimitFullSubcategoryInclusionOfClosed J P F

Depends on / 依赖: createsColimitFullSubcategoryInclusionOfClosed
-/
instance createsColimitsOfShapeFullSubcategoryInclusion [P.IsClosedUnderColimitsOfShape J]
    [HasColimitsOfShape J C] : CreatesColimitsOfShape J P.ι where
  CreatesColimit := @fun F => createsColimitFullSubcategoryInclusionOfClosed J P F

/--
theorem `hasColimit_of_closedUnderColimits` / 定理 `hasColimit_of_closedUnderColimits`

English:
theorem hasColimit_of_closedUnderColimits
  statement: [P.IsClosedUnderColimitsOfShape J]
  proof: have : CreatesColimit F P.ι :=
    createsColimitFullSubcategoryInclusionOfClosed J P F
  hasColimit_of_created F P.ι

中文:
定理 hasColimit_of_closedUnderColimits
  结论: [P.是ClosedUnderColimitsOfShape J]
  证明: have : CreatesColimit F P.ι :=
    createsColimitFullSubcategoryInclusionOfClosed J P F
  hasColimit_of_created F P.ι

Depends on / 依赖: CreatesColimit, createsColimitFullSubcategoryInclusionOfClosed, hasColimit_of_created
-/
theorem hasColimit_of_closedUnderColimits [P.IsClosedUnderColimitsOfShape J]
    (F : J ⥤ P.FullSubcategory) [HasColimit (F ⋙ P.ι)] : HasColimit F :=
  have : CreatesColimit F P.ι :=
    createsColimitFullSubcategoryInclusionOfClosed J P F
  hasColimit_of_created F P.ι

/--
Instance `hasColimitsOfShape_of_closedUnderColimits` / 实例 `hasColimitsOfShape_of_closedUnderColimits`

English:
instance hasColimitsOfShape_of_closedUnderColimits
  signature: [P.IsClosedUnderColimitsOfShape J]
  body: { has_colimit := fun F => hasColimit_of_closedUnderColimits J P F }

中文:
实例 hasColimitsOfShape_of_closedUnderColimits
  签名: [P.是ClosedUnderColimitsOfShape J]
  定义体: { has_colimit := fun F => hasColimit_of_closedUnderColimits J P F }

Depends on / 依赖: hasColimit_of_closedUnderColimits, has_colimit
-/
instance hasColimitsOfShape_of_closedUnderColimits [P.IsClosedUnderColimitsOfShape J]
    [HasColimitsOfShape J C] : HasColimitsOfShape J P.FullSubcategory :=
  { has_colimit := fun F => hasColimit_of_closedUnderColimits J P F }

end Limits

namespace ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C) (J : Type w) [Category.{w'} J]

/--
lemma `isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι` / 引理 `isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι`

English:
lemma isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι
  proof: by
    rintro X ⟨p⟩
    exact P.prop_of_iso (IsColimit.coconePointUniqueUpToIso
      (isColimitOfPreserves P.ι (colimit.isColimit (P.lift p.diag p.prop_diag_obj)))
        p.isColimit) (colimit (P.lift p.diag p.prop_diag_obj)).property

中文:
引理 isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι
  证明: by
    rintro X ⟨p⟩
    exact P.prop_of_iso (IsColimit.coconePointUniqueUpToIso
      (isColimitOfPreserves P.ι (colimit.isColimit (P.lift p.diag p.prop_diag_obj)))
        p.isColimit) (colimit (P.lift p.diag p.prop_diag_obj)).property

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, P.lift, P.prop_of_iso, coconePointUniqueUpToIso, colimit, colimit.isColimit, isColimit, isColimitOfPreserves, p.diag, p.isColimit, p.prop_diag_obj, prop_diag_obj, prop_of_iso, property
-/
lemma isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι
    [HasColimitsOfShape J P.FullSubcategory] [P.IsClosedUnderIsomorphisms]
    [PreservesColimitsOfShape J P.ι] :
    P.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    exact P.prop_of_iso (IsColimit.coconePointUniqueUpToIso
      (isColimitOfPreserves P.ι (colimit.isColimit (P.lift p.diag p.prop_diag_obj)))
        p.isColimit) (colimit (P.lift p.diag p.prop_diag_obj)).property

/--
lemma `isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι` / 引理 `isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι`

English:
lemma isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι
  proof: by
    rintro X ⟨p⟩
    exact P.prop_of_iso (IsLimit.conePointUniqueUpToIso
      (isLimitOfPreserves P.ι (limit.isLimit (P.lift p.diag p.prop_diag_obj)))
        p.isLimit) (limit (P.lift p.diag p.prop_diag_obj)).property

中文:
引理 isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι
  证明: by
    rintro X ⟨p⟩
    exact P.prop_of_iso (IsLimit.conePointUniqueUpToIso
      (isLimitOfPreserves P.ι (limit.isLimit (P.lift p.diag p.prop_diag_obj)))
        p.isLimit) (limit (P.lift p.diag p.prop_diag_obj)).property

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, P.lift, P.prop_of_iso, conePointUniqueUpToIso, isLimit, isLimitOfPreserves, limit.isLimit, p.diag, p.isLimit, p.prop_diag_obj, prop_diag_obj, prop_of_iso, property
-/
lemma isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι
    [HasLimitsOfShape J P.FullSubcategory] [P.IsClosedUnderIsomorphisms]
    [PreservesLimitsOfShape J P.ι] :
    P.IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    exact P.prop_of_iso (IsLimit.conePointUniqueUpToIso
      (isLimitOfPreserves P.ι (limit.isLimit (P.lift p.diag p.prop_diag_obj)))
        p.isLimit) (limit (P.lift p.diag p.prop_diag_obj)).property

end ObjectProperty

variable {J : Type w} [Category.{w'} J]
variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (F : C ⥤ D)

namespace Limits

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimitsOfShape
  signature: J C] [PreservesLimitsOfShape J F] [F.Full] [F.Faithful] :
  body: .mk' (by
    rintro _ ⟨G, hG⟩
    exact ⟨limit (Functor.essImage.liftFunctor G F hG),
      ⟨IsLimit.conePointsIsoOfNatIso
        (isLimitOfPreserves F (limit.isLimit _)) (limit.isLimit _)
        (Functor.essImage.liftFunctorCompIso _ _ _)⟩⟩)

中文:
实例 [有形状极限
  签名: J C] [保持形状极限 J F] [F.满] [F.忠实] :
  定义体: .mk' (by
    rintro _ ⟨G, hG⟩
    exact ⟨limit (Functor.essImage.liftFunctor G F hG),
      ⟨IsLimit.conePointsIsoOfNatIso
        (isLimitOfPreserves F (limit.isLimit _)) (limit.isLimit _)
        (Functor.essImage.liftFunctorCompIso _ _ _)⟩⟩)

Depends on / 依赖: Functor, Functor.essImage.liftFunctor, Functor.essImage.liftFunctorCompIso, IsLimit, IsLimit.conePointsIsoOfNatIso, conePointsIsoOfNatIso, essImage, isLimit, isLimitOfPreserves, liftFunctor, liftFunctorCompIso, limit.isLimit
-/
instance [HasLimitsOfShape J C] [PreservesLimitsOfShape J F] [F.Full] [F.Faithful] :
    F.essImage.IsClosedUnderLimitsOfShape J :=
  .mk' (by
    rintro _ ⟨G, hG⟩
    exact ⟨limit (Functor.essImage.liftFunctor G F hG),
      ⟨IsLimit.conePointsIsoOfNatIso
        (isLimitOfPreserves F (limit.isLimit _)) (limit.isLimit _)
        (Functor.essImage.liftFunctorCompIso _ _ _)⟩⟩)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimitsOfShape
  signature: J C] [PreservesColimitsOfShape J F] [F.Full] [F.Faithful] :
  body: .mk' (by
    rintro _ ⟨G, hG⟩
    exact ⟨colimit (Functor.essImage.liftFunctor G F hG),
      ⟨IsColimit.coconePointsIsoOfNatIso
        (isColimitOfPreserves F (colimit.isColimit _)) (colimit.isColimit _)
        (Functor.essImage.liftFunctorCompIso _ _ _)⟩⟩)

中文:
实例 [有形状余极限
  签名: J C] [保持形状余极限 J F] [F.满] [F.忠实] :
  定义体: .mk' (by
    rintro _ ⟨G, hG⟩
    exact ⟨colimit (Functor.essImage.liftFunctor G F hG),
      ⟨IsColimit.coconePointsIsoOfNatIso
        (isColimitOfPreserves F (colimit.isColimit _)) (colimit.isColimit _)
        (Functor.essImage.liftFunctorCompIso _ _ _)⟩⟩)

Depends on / 依赖: Functor, Functor.essImage.liftFunctor, Functor.essImage.liftFunctorCompIso, IsColimit, IsColimit.coconePointsIsoOfNatIso, coconePointsIsoOfNatIso, colimit, colimit.isColimit, essImage, isColimit, isColimitOfPreserves, liftFunctor, liftFunctorCompIso
-/
instance [HasColimitsOfShape J C] [PreservesColimitsOfShape J F] [F.Full] [F.Faithful] :
    F.essImage.IsClosedUnderColimitsOfShape J :=
  .mk' (by
    rintro _ ⟨G, hG⟩
    exact ⟨colimit (Functor.essImage.liftFunctor G F hG),
      ⟨IsColimit.coconePointsIsoOfNatIso
        (isColimitOfPreserves F (colimit.isColimit _)) (colimit.isColimit _)
        (Functor.essImage.liftFunctorCompIso _ _ _)⟩⟩)

end CategoryTheory.Limits
