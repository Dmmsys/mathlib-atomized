/-
Copyright (c) 2026 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jonas van der Schaaf
-/
module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!

# Preservation of (co)limits by the sheaf Yoneda functor
-/

public section

open CategoryTheory Functor Limits GrothendieckTopology

universe v' v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [Subcanonical J]
  {K : Type*} [Category* K]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F : K ⥤ C} [∀ X : Sheaf J (Type v), PreservesLimit F.op X.obj] :
    PreservesColimit F J.yoneda where
  preserves {c} hc := ⟨by
    suffices IsLimit (coyoneda.mapCone (J.yoneda.mapCocone c).op) from
      isColimitOfOp (isLimitOfReflects _ this)
    apply evaluationJointlyReflectsLimits
    intro X
    suffices IsLimit ((X.obj ⋙ uliftFunctor).mapCone c.op) from IsLimit.mapConeEquiv
      (isoWhiskerRight (J.yonedaOpCompCoyoneda) ((evaluation _ _ ).obj X)).symm this
    exact isLimitOfPreserves _ hc.op⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ X : Sheaf J (Type v), PreservesLimitsOfShape Kᵒᵖ X.obj] :
    PreservesColimitsOfShape K J.yoneda where
  preservesColimit := inferInstance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F : K ⥤ C} [∀ X : Sheaf J (Type max v v'), PreservesLimit F.op X.obj] :
    PreservesColimit F (uliftYoneda.{v'} J) where
  preserves {c} hc := ⟨by
    suffices IsLimit (coyoneda.mapCone (J.uliftYoneda.mapCocone c).op) from
      isColimitOfOp (isLimitOfReflects _ this)
    apply evaluationJointlyReflectsLimits
    intro X
    suffices IsLimit ((X.obj ⋙ uliftFunctor).mapCone c.op) from IsLimit.mapConeEquiv
      (isoWhiskerRight (J.uliftYonedaOpCompCoyoneda) ((evaluation _ _ ).obj X)).symm this
    exact isLimitOfPreserves _ hc.op⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ X : Sheaf J (Type max v v'), PreservesLimitsOfShape Kᵒᵖ X.obj] :
    PreservesColimitsOfShape K (uliftYoneda.{v'} J) where
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesLimitsOfShape K J.yoneda where
  preservesLimit := by
    intro F
    have : PreservesLimitsOfShape K (J.yoneda ⋙ sheafToPresheaf J (Type v)) :=
      preservesLimitsOfShape_of_natIso (yonedaCompSheafToPresheaf J).symm
    exact preservesLimit_of_reflects_of_preserves (F := J.yoneda) (G := sheafToPresheaf ..)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesLimitsOfShape K (uliftYoneda.{v'} J) where
  preservesLimit := by
    intro F
    have : PreservesLimitsOfShape K (uliftYoneda J ⋙ sheafToPresheaf J (Type max v v')) :=
      preservesLimitsOfShape_of_natIso (uliftYonedaCompSheafToPresheaf J).symm
    exact preservesLimit_of_reflects_of_preserves (uliftYoneda J)
      (sheafToPresheaf ..)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F : K ⥤ C} [∀ X : Sheaf J (Type v), PreservesLimit F.op X.obj] :
    PreservesColimit F J.yoneda :=
  preservesColimit_of_natIso _ J.uliftYonedaIsoYoneda
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ X : Sheaf J (Type v), PreservesFiniteProducts X.obj] :
    PreservesFiniteCoproducts J.yoneda where
  preserves _ := inferInstance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ X : Sheaf J (Type max v v'), PreservesFiniteProducts X.obj] :
    PreservesFiniteCoproducts (uliftYoneda.{v'} J) where
  preserves _ := inferInstance
