/-
Copyright (c) 2026 Thomas Browning, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Christian Merten
-/
module

public import Mathlib.Algebra.Group.Invertible.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Cartesian.ShrinkYoneda
public import Mathlib.CategoryTheory.Monoidal.Internal.Limits

/-!
# Limits in `Grp C`

We show that `Grp C` has limits.
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor Grp Limits MonObj

universe w v

variable {C : Type*} [Category.{v} C] [CartesianMonoidalCategory C]
  {J : Type w} [Category J] [HasLimitsOfShape J C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimitsOfShape J (shrinkYonedaMon.{max w v} (C := C))
  body: have : PreservesLimitsOfShape J (shrinkYonedaMon ⋙ (whiskeringRight _ _ _).obj (forget MonCat)) :=
    (inferInstance : PreservesLimitsOfShape J (Mon.forget C ⋙ shrinkYoneda.{max w v}))
  preservesLimitsOfShape_of_reflects_of_preserves _ ((whiskeringRight _ _ _).obj (forget MonCat))

中文:
实例 :
  签名: PreservesLimitsOfShape J (shrinkYonedaMon.{max w v} (C := C))
  定义体: have : PreservesLimitsOfShape J (shrinkYonedaMon ⋙ (whiskeringRight _ _ _).obj (forget MonCat)) :=
    (inferInstance : PreservesLimitsOfShape J (Mon.forget C ⋙ shrinkYoneda.{max w v}))
  preservesLimitsOfShape_of_reflects_of_preserves _ ((whiskeringRight _ _ _).obj (forget MonCat))
-/
instance : PreservesLimitsOfShape J (shrinkYonedaMon.{max w v} (C := C)) :=
  have : PreservesLimitsOfShape J (shrinkYonedaMon ⋙ (whiskeringRight _ _ _).obj (forget MonCat)) :=
    (inferInstance : PreservesLimitsOfShape J (Mon.forget C ⋙ shrinkYoneda.{max w v}))
  preservesLimitsOfShape_of_reflects_of_preserves _ ((whiskeringRight _ _ _).obj (forget MonCat))

/--
Definition of `Grp.limitAux` / `Grp.limitAux` 的定义

English:
definition Grp.limitAux
  signature: (F : J ⥤ Grp C)
  body: (limit (F ⋙ forget₂Mon C)).X
  grp := GrpObj.ofInvertible (limit (F ⋙ forget₂Mon C)).X fun X f =>
letI e := Shrink.mulEquiv.symm.trans Iso.monCatIsoToMulEquiv
      preservesLimitIso (shrinkYonedaMon ⋙ (evaluation _ _).obj (.op X))
      (F ⋙ forget₂Mon C) ≪≫ (preservesLimitIso (forget₂ GrpCat MonCa

中文:
定义 Grp.limitAux
  签名: (F : J ⥤ Grp C)
  定义体: (limit (F ⋙ forget₂Mon C)).X
  grp := GrpObj.ofInvertible (limit (F ⋙ forget₂Mon C)).X fun X f =>
letI e := Shrink.mulEquiv.symm.trans Iso.monCatIsoToMulEquiv
      preservesLimitIso (shrinkYonedaMon ⋙ (evaluation _ _).obj (.op X))
      (F ⋙ forget₂Mon C) ≪≫ (preservesLimitIso (forget₂ GrpCat MonCa
-/
noncomputable def Grp.limitAux (F : J ⥤ Grp C) : Grp C where
  X := (limit (F ⋙ forget₂Mon C)).X
  grp := GrpObj.ofInvertible (limit (F ⋙ forget₂Mon C)).X fun X f =>
letI e := Shrink.mulEquiv.symm.trans Iso.monCatIsoToMulEquiv
      preservesLimitIso (shrinkYonedaMon ⋙ (evaluation _ _).obj (.op X))
      (F ⋙ forget₂Mon C) ≪≫ (preservesLimitIso (forget₂ GrpCat MonCat)
        (F ⋙ shrinkYonedaGrp.{max w v} ⋙ (evaluation _ _).obj (.op X))).symm
    letI := (limit (F ⋙ shrinkYonedaGrp.{max w v} ⋙ (evaluation _ _).obj (.op X))).str
    ((invertibleOfGroup (e f)).map e.symm).copy f (e.symm_apply_apply f).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CreatesLimitsOfShape J (forget₂Mon C)
  body: createsLimitOfFullyFaithfulOfIso (limitAux F) (.refl (limitAux F).toMon)

中文:
实例 :
  签名: CreatesLimitsOfShape J (forget₂Mon C)
  定义体: createsLimitOfFullyFaithfulOfIso (limitAux F) (.refl (limitAux F).toMon)

Depends on / 依赖: createsLimitOfFullyFaithfulOfIso, limitAux
-/
noncomputable instance : CreatesLimitsOfShape J (forget₂Mon C) where
  CreatesLimit {F} := createsLimitOfFullyFaithfulOfIso (limitAux F) (.refl (limitAux F).toMon)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CreatesLimitsOfShape J (Grp.forget C)
  body: inferInstanceAs CreatesLimitsOfShape J (forget₂Mon C ⋙ Mon.forget C)

中文:
实例 :
  签名: CreatesLimitsOfShape J (Grp.forget C)
  定义体: inferInstanceAs CreatesLimitsOfShape J (forget₂Mon C ⋙ Mon.forget C)

Depends on / 依赖: CreatesLimitsOfShape, Mon.forget, forget
-/
noncomputable instance : CreatesLimitsOfShape J (Grp.forget C) :=
inferInstanceAs CreatesLimitsOfShape J (forget₂Mon C ⋙ Mon.forget C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLimitsOfShape J (Grp C)
  body: hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (Grp.forget C)

中文:
实例 :
  签名: HasLimitsOfShape J (Grp C)
  定义体: hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (Grp.forget C)

Depends on / 依赖: Grp.forget, forget, hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
-/
instance : HasLimitsOfShape J (Grp C) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (Grp.forget C)

end CategoryTheory
