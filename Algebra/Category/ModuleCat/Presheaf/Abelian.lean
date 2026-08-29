/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# The category of presheaves of modules is abelian

-/

public section

universe v v₁ u₁ u

open CategoryTheory Category Limits

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] (R : Cᵒᵖ ⥤ RingCat.{u})

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsNormalEpiCategory (PresheafOfModules.{v} R)
  body: ⟨NormalEpi.mk _ (kernel.ι p) (kernel.condition _)
    (evaluationJointlyReflectsColimits _ _ (fun _ =>
      Abelian.isColimitMapCoconeOfCokernelCoforkOfπ _ _))⟩

中文:
实例 :
  签名: IsNormalEpiCategory (PresheafOfModules.{v} R)
  定义体: ⟨NormalEpi.mk _ (kernel.ι p) (kernel.condition _)
    (evaluationJointlyReflectsColimits _ _ (fun _ =>
      Abelian.isColimitMapCoconeOfCokernelCoforkOfπ _ _))⟩

Depends on / 依赖: NormalEpi, NormalEpi.mk, condition, kernel, kernel.condition
-/
noncomputable instance : IsNormalEpiCategory (PresheafOfModules.{v} R) where
  normalEpiOfEpi p _ := ⟨NormalEpi.mk _ (kernel.ι p) (kernel.condition _)
    (evaluationJointlyReflectsColimits _ _ (fun _ =>
      Abelian.isColimitMapCoconeOfCokernelCoforkOfπ _ _))⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsNormalMonoCategory (PresheafOfModules.{v} R)
  body: ⟨NormalMono.mk _ (cokernel.π i) (cokernel.condition _)
    (evaluationJointlyReflectsLimits _ _ (fun _ =>
      Abelian.isLimitMapConeOfKernelForkOfι _ _))⟩

中文:
实例 :
  签名: IsNormalMonoCategory (PresheafOfModules.{v} R)
  定义体: ⟨NormalMono.mk _ (cokernel.π i) (cokernel.condition _)
    (evaluationJointlyReflectsLimits _ _ (fun _ =>
      Abelian.isLimitMapConeOfKernelForkOfι _ _))⟩

Depends on / 依赖: NormalMono, NormalMono.mk, cokernel, cokernel.condition, condition
-/
noncomputable instance : IsNormalMonoCategory (PresheafOfModules.{v} R) where
  normalMonoOfMono i _ := ⟨NormalMono.mk _ (cokernel.π i) (cokernel.condition _)
    (evaluationJointlyReflectsLimits _ _ (fun _ =>
      Abelian.isLimitMapConeOfKernelForkOfι _ _))⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Abelian (PresheafOfModules.{v} R)

中文:
实例 :
  签名: Abelian (PresheafOfModules.{v} R)
-/
noncomputable instance : Abelian (PresheafOfModules.{v} R) where

end PresheafOfModules
