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

/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : IsNormalEpiCategory (PresheafOfModules.{v} R) where
  normalEpiOfEpi p _ := ⟨NormalEpi.mk _ (kernel.ι p) (kernel.condition _)
    (evaluationJointlyReflectsColimits _ _ (fun _ =>
      Abelian.isColimitMapCoconeOfCokernelCoforkOfπ _ _))⟩
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : IsNormalMonoCategory (PresheafOfModules.{v} R) where
  normalMonoOfMono i _ := ⟨NormalMono.mk _ (cokernel.π i) (cokernel.condition _)
    (evaluationJointlyReflectsLimits _ _ (fun _ =>
      Abelian.isLimitMapConeOfKernelForkOfι _ _))⟩
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Abelian (PresheafOfModules.{v} R) where

end PresheafOfModules

