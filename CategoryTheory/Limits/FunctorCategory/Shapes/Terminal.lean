/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Initial and terminal objects in the category of functors

We show that if a functor `F : C ⥤ D` is such that `F.obj X`
is terminal for all `X`, then `F` is a terminal object.

-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits

variable {C D : Type*} [Category* C] [Category* D]

/--
Definition of `isTerminal` / `isTerminal` 的定义

English:
definition isTerminal
  signature: {F : C ⥤ D} (hF : forall (X : C), IsTerminal (F.obj X))
  body: by
  refine evaluationJointlyReflectsLimits _
    fun X => IsLimit.equivOfNatIsoOfIso (Functor.emptyExt _ _) _ _ ?_ (hF X)
  exact Cone.ext (Iso.refl _)

中文:
定义 isTerminal
  签名: {F : C ⥤ D} (hF : 对任意 (X : C), IsTerminal (F.obj X))
  定义体: by
  refine evaluationJointlyReflectsLimits _
    fun X => IsLimit.equivOfNatIsoOfIso (Functor.emptyExt _ _) _ _ ?_ (hF X)
  exact Cone.ext (Iso.refl _)

Depends on / 依赖: Cone.ext, Functor, Functor.emptyExt, IsLimit, IsLimit.equivOfNatIsoOfIso, Iso.refl, emptyExt, equivOfNatIsoOfIso, evaluationJointlyReflectsLimits
-/
def isTerminal {F : C ⥤ D} (hF : forall (X : C), IsTerminal (F.obj X)) :
    IsTerminal F := by
  refine evaluationJointlyReflectsLimits _
    fun X => IsLimit.equivOfNatIsoOfIso (Functor.emptyExt _ _) _ _ ?_ (hF X)
  exact Cone.ext (Iso.refl _)

/--
Definition of `isInitial` / `isInitial` 的定义

English:
definition isInitial
  signature: {F : C ⥤ D} (hF : forall (X : C), IsInitial (F.obj X))
  body: by
  refine evaluationJointlyReflectsColimits _
    fun X => IsColimit.equivOfNatIsoOfIso (Functor.emptyExt _ _) _ _ ?_ (hF X)
  exact Cocone.ext (Iso.refl _)

中文:
定义 isInitial
  签名: {F : C ⥤ D} (hF : 对任意 (X : C), IsInitial (F.obj X))
  定义体: by
  refine evaluationJointlyReflectsColimits _
    fun X => IsColimit.equivOfNatIsoOfIso (Functor.emptyExt _ _) _ _ ?_ (hF X)
  exact Cocone.ext (Iso.refl _)

Depends on / 依赖: Cocone, Cocone.ext, Functor, Functor.emptyExt, IsColimit, IsColimit.equivOfNatIsoOfIso, Iso.refl, emptyExt, equivOfNatIsoOfIso, evaluationJointlyReflectsColimits
-/
def isInitial {F : C ⥤ D} (hF : forall (X : C), IsInitial (F.obj X)) :
    IsInitial F := by
  refine evaluationJointlyReflectsColimits _
    fun X => IsColimit.equivOfNatIsoOfIso (Functor.emptyExt _ _) _ _ ?_ (hF X)
  exact Cocone.ext (Iso.refl _)

end CategoryTheory.Functor
