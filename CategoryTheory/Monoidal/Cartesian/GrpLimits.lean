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

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesLimitsOfShape J (shrinkYonedaMon.{max w v} (C := C)) :=
  have : PreservesLimitsOfShape J (shrinkYonedaMon ⋙ (whiskeringRight _ _ _).obj (forget MonCat)) :=
    (inferInstance : PreservesLimitsOfShape J (Mon.forget C ⋙ shrinkYoneda.{max w v}))
  preservesLimitsOfShape_of_reflects_of_preserves _ ((whiskeringRight _ _ _).obj (forget MonCat))

/-- An auxiliary construction in order to prove that `Grp.forget₂Mon` creates limits. -/
/-
**CategoryTheory.Grp.limitAux** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grp`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v, u_1} C] →     [inst
_1 : CategoryTheory.CartesianMonoidalCategory C] →       {J : Type w} →         
[inst_2 : CategoryTheory.Category.{u_2, w} J] →           [CategoryTheory.Limits
.HasLimitsOfShape J C] →             CategoryTheory.Functor J (CategoryTheory.Gr
p C) → CategoryTheory.Grp C
参数：CategoryTheory.Grp C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary construction in order to prove that `Grp.forget₂Mon` creates limits
.
-/
noncomputable def Grp.limitAux (F : J ⥤ Grp C) : Grp C where
  X := (limit (F ⋙ forget₂Mon C)).X
  grp := GrpObj.ofInvertible (limit (F ⋙ forget₂Mon C)).X fun X f ↦
    letI e := Shrink.mulEquiv.symm.trans <| Iso.monCatIsoToMulEquiv <|
      preservesLimitIso (shrinkYonedaMon ⋙ (evaluation _ _).obj (.op X))
      (F ⋙ forget₂Mon C) ≪≫ (preservesLimitIso (forget₂ GrpCat MonCat)
        (F ⋙ shrinkYonedaGrp.{max w v} ⋙ (evaluation _ _).obj (.op X))).symm
    letI := (limit (F ⋙ shrinkYonedaGrp.{max w v} ⋙ (evaluation _ _).obj (.op X))).str
    ((invertibleOfGroup (e f)).map e.symm).copy f (e.symm_apply_apply f).symm
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : CreatesLimitsOfShape J (forget₂Mon C) where
  CreatesLimit {F} := createsLimitOfFullyFaithfulOfIso (limitAux F) (.refl (limitAux F).toMon)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : CreatesLimitsOfShape J (Grp.forget C) :=
  inferInstanceAs <| CreatesLimitsOfShape J (forget₂Mon C ⋙ Mon.forget C)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasLimitsOfShape J (Grp C) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (Grp.forget C)

end CategoryTheory

