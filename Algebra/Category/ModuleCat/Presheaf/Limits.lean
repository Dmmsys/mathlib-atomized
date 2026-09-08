/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Limits in categories of presheaves of modules

In this file, it is shown that under suitable assumptions,
limits exist in the category `PresheafOfModules R`.

-/

@[expose] public section

universe v v₁ v₂ u₁ u₂ u u'

open CategoryTheory Category Limits

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {J : Type u₂} [Category.{v₂} J]
  (F : J ⥤ PresheafOfModules.{v} R)

section Limits

variable [∀ X, Small.{v} ((F ⋙ evaluation R X) ⋙ forget _).sections]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A cone in the category `PresheafOfModules R` is limit if it is so after the application
of the functors `evaluation R X` for all `X`. -/
/-
**PresheafOfModules.evaluationJointlyReflectsLimits** 是 Mathlib 中的一个定义，位于命名空间 `P
resheafOfModules`。
形式化陈述：evaluationJointlyReflectsLimits (c : Cone F) (hc : forall (X : Cᵒᵖ), IsLim
it ((evaluation R X).mapCone c)) : IsLimit c where lift s
参数：c : Cone F；hc : forall (X : Cᵒᵖ), IsLimit ((evaluation R X).mapCone c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cone in the category `PresheafOfModules R` is limit if it is so after the appl
ication
of the functors `evaluation R X` for all `X`.
-/
def evaluationJointlyReflectsLimits (c : Cone F)
    (hc : ∀ (X : Cᵒᵖ), IsLimit ((evaluation R X).mapCone c)) : IsLimit c where
  lift s :=
    { app := fun X => (hc X).lift ((evaluation R X).mapCone s)
      naturality := fun {X Y} f ↦ by
        apply (isLimitOfPreserves (ModuleCat.restrictScalars (R.map f).hom) (hc Y)).hom_ext
        intro j
        have h₁ := (c.π.app j).naturality f
        have h₂ := (hc X).fac ((evaluation R X).mapCone s) j
        rw [Functor.mapCone_π_app, assoc, assoc, ← Functor.map_comp, IsLimit.fac]
        dsimp at h₁ h₂ ⊢
        rw [h₁, reassoc_of% h₂, Hom.naturality] }
  fac s j := by
    ext1 X
    exact (hc X).fac ((evaluation R X).mapCone s) j
  uniq s m hm := by
    ext1 X
    apply (hc X).uniq ((evaluation R X).mapCone s)
    intro j
    dsimp
    rw [← hm, comp_app]
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    HasLimit (F ⋙ evaluation R Y ⋙ ModuleCat.restrictScalars (R.map f).hom) := by
  change HasLimit ((F ⋙ evaluation R Y) ⋙ ModuleCat.restrictScalars (R.map f).hom)
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given `F : J ⥤ PresheafOfModules.{v} R`, this is the presheaf of modules obtained by
taking a limit in the category of modules over `R.obj X` for all `X`. -/
@[simps]
/-
**PresheafOfModules.limitPresheafOfModules** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOf
Modules`。
形式化陈述：limitPresheafOfModules : PresheafOfModules R where obj X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PresheafOfModules.instHasLimitModuleCatCarrierObjOppositeRingCatCompEval
uationRestrictScalarsHomMap`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁
, u₁} C] {R : CategoryTheory.Functor Cᵒᵖ RingCat} {J : Type u₂}   [inst_1 : Cate
goryTheor…

--- 原说明 ---
Given `F : J ⥤ PresheafOfModules.{v} R`, this is the presheaf of modules obtaine
d by
taking a limit in the category of modules over `R.obj X` for all `X`.
-/
noncomputable def limitPresheafOfModules : PresheafOfModules R where
  obj X := limit (F ⋙ evaluation R X)
  map {_ Y} f := limMap (Functor.whiskerLeft F (restriction R f)) ≫
    (preservesLimitIso (ModuleCat.restrictScalars (R.map f).hom) (F ⋙ evaluation R Y)).inv
  map_id X := by
    dsimp
    rw [← cancel_mono (preservesLimitIso _ _).hom, assoc, Iso.inv_hom_id, comp_id]
    apply limit.hom_ext
    simp [← Functor.assoc, ← ModuleCat.restrictScalarsId'App_inv_naturality,
      ModuleCat.restrictScalarsId'_inv_app]
  map_comp {X Y Z} f g := by
    dsimp
    rw [← cancel_mono (preservesLimitIso _ _).hom, assoc, assoc, assoc, assoc, Iso.inv_hom_id,
      comp_id]
    apply limit.hom_ext
    intro j
    simp only [Functor.map_comp, assoc, ← Functor.assoc, preservesLimitIso_hom_π,
      ← ModuleCat.restrictScalarsComp'App_inv_naturality]
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, assoc, preservesLimitIso_inv_π]
    simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The (limit) cone for `F : J ⥤ PresheafOfModules.{v} R` that is constructed from the limit
of `F ⋙ evaluation R X` for all `X`. -/
@[simps]
/-
**PresheafOfModules.limitCone** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：limitCone : Cone F where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (limit) cone for `F : J ⥤ PresheafOfModules.{v} R` that is constructed from 
the limit
of `F ⋙ evaluation R X` for all `X`.
-/
noncomputable def limitCone : Cone F where
  pt := limitPresheafOfModules F
  π :=
    { app := fun j ↦
        { app := fun X ↦ limit.π (F ⋙ evaluation R X) j
          naturality := fun {X Y} f ↦ by
            dsimp
            simp only [assoc, preservesLimitIso_inv_π]
            apply limMap_π }
      naturality := fun {j j'} f ↦ by
        ext1 X
        simpa using (limit.w (F ⋙ evaluation R X) f).symm }

/-- The cone `limitCone F` is limit for any `F : J ⥤ PresheafOfModules.{v} R`. -/
/-
**PresheafOfModules.isLimitLimitCone** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModule
s`。
形式化陈述：isLimitLimitCone : IsLimit (limitCone F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cone `limitCone F` is limit for any `F : J ⥤ PresheafOfModules.{v} R`.
-/
noncomputable def isLimitLimitCone : IsLimit (limitCone F) :=
  evaluationJointlyReflectsLimits _ _ (fun _ => limit.isLimit _)
/-
**PresheafOfModules.hasLimit** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
形式化陈述：hasLimit : HasLimit F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasLimit : HasLimit F := ⟨_, isLimitLimitCone F⟩
/-
**PresheafOfModules.evaluation_preservesLimit** 是 Mathlib 中的一个实例，位于命名空间 `Preshea
fOfModules`。
形式化陈述：evaluation_preservesLimit (X : Cᵒᵖ) : PreservesLimit F (evaluation R X)
参数：X : Cᵒᵖ。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
-/
noncomputable instance evaluation_preservesLimit (X : Cᵒᵖ) :
    PreservesLimit F (evaluation R X) :=
  preservesLimit_of_preserves_limit_cone (isLimitLimitCone F) (limit.isLimit _)
/-
**PresheafOfModules.toPresheaf_preservesLimit** 是 Mathlib 中的一个实例，位于命名空间 `Preshea
fOfModules`。
形式化陈述：toPresheaf_preservesLimit : PreservesLimit F (toPresheaf R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
-/
noncomputable instance toPresheaf_preservesLimit :
    PreservesLimit F (toPresheaf R) :=
  preservesLimit_of_preserves_limit_cone (isLimitLimitCone F)
    (Limits.evaluationJointlyReflectsLimits _
      (fun X => isLimitOfPreserves (evaluation R X ⋙ forget₂ _ AddCommGrpCat)
        (isLimitLimitCone F)))

end Limits

variable (R J)

section Small

variable [Small.{v} J]

/-
**PresheafOfModules.hasLimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `PresheafOfModule
s`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (R : CategoryT
heory.Functor Cᵒᵖ RingCat) (J : Type u₂)   [inst_1 : CategoryTheory.Category.{v₂
, u₂} J] [Small.{v, u₂} J],   CategoryTheory.Limits.HasLimitsOfShape J (Presheaf
OfModules R)
参数：R : CategoryTheory.Functor Cᵒᵖ RingCat；J : Type u₂；PresheafOfModules R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
instance hasLimitsOfShape : HasLimitsOfShape J (PresheafOfModules.{v} R) where
/-
**PresheafOfModules.hasLimitsOfSize** 是 Mathlib 中的一个定理，位于命名空间 `PresheafOfModules
`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (R : CategoryT
heory.Functor Cᵒᵖ RingCat),   CategoryTheory.Limits.HasLimitsOfSize.{v, v, max u
₁ v, max (max (max (v + 1) u) u₁) v₁} (PresheafOfModules R)
参数：R : CategoryTheory.Functor Cᵒᵖ RingCat；max (max (v + 1) u) u₁；PresheafOfModul
es R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PresheafOfModules.hasLimitsOfShape`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] (R : CategoryTheory.Functor Cᵒᵖ RingCat) (J : Type u₂)  
 [inst_1 : CategoryTheor…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
instance hasLimitsOfSize : HasLimitsOfSize.{v, v} (PresheafOfModules.{v} R) where
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Cᵒᵖ) : PreservesLimitsOfShape J (evaluation.{v} R X) where
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Cᵒᵖ) : PreservesLimitsOfSize.{v, v} (evaluation.{v} R X) where
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesLimitsOfShape J (toPresheaf.{v} R) where
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesLimitsOfSize.{v, v} (toPresheaf.{v} R) where

end Small

section Finite

/-
**PresheafOfModules.hasFiniteLimits** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules
`。
形式化陈述：hasFiniteLimits : HasFiniteLimits (PresheafOfModules.{v} R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `PresheafOfModules.hasLimitsOfShape`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] (R : CategoryTheory.Functor Cᵒᵖ RingCat) (J : Type u₂)  
 [inst_1 : CategoryTheor…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
instance hasFiniteLimits : HasFiniteLimits (PresheafOfModules.{v} R) :=
  ⟨fun _ => inferInstance⟩
/-
**PresheafOfModules.evaluation_preservesFiniteLimits** 是 Mathlib 中的一个定理，位于命名空间 `
PresheafOfModules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (R : CategoryT
heory.Functor Cᵒᵖ RingCat) (X : Cᵒᵖ),   CategoryTheory.Limits.PreservesFiniteLim
its (PresheafOfModules.evaluation R X)
参数：R : CategoryTheory.Functor Cᵒᵖ RingCat；X : Cᵒᵖ；PresheafOfModules.evaluation R
 X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PresheafOfModules.instPreservesLimitsOfShapeModuleCatCarrierObjOppositeR
ingCatEvaluation`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (R
 : CategoryTheory.Functor Cᵒᵖ RingCat) (J : Type u₂)   [inst_1 : CategoryTheor…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
noncomputable instance evaluation_preservesFiniteLimits (X : Cᵒᵖ) :
    PreservesFiniteLimits (evaluation.{v} R X) where
/-
**PresheafOfModules.toPresheaf_preservesFiniteLimits** 是 Mathlib 中的一个定理，位于命名空间 `
PresheafOfModules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (R : CategoryT
heory.Functor Cᵒᵖ RingCat),   CategoryTheory.Limits.PreservesFiniteLimits (Presh
eafOfModules.toPresheaf R)
参数：R : CategoryTheory.Functor Cᵒᵖ RingCat；PresheafOfModules.toPresheaf R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PresheafOfModules.instPreservesLimitsOfShapeFunctorOppositeAbToPresheaf`
：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (R : CategoryTheory
.Functor Cᵒᵖ RingCat) (J : Type u₂)   [inst_1 : CategoryTheor…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
noncomputable instance toPresheaf_preservesFiniteLimits :
    PreservesFiniteLimits (toPresheaf.{v} R) where

end Finite

end PresheafOfModules

