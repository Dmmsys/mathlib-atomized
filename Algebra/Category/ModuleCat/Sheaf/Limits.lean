/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.Limits

/-! # Limits in categories of sheaves of modules

In this file, it is shown that under suitable assumptions,
limits exist in the category `SheafOfModules R`.

## TODO
* do the same for colimits (which requires constructing the associated sheaf of modules functor)

-/

public section

universe v v₁ v₂ u₁ u₂ u

open CategoryTheory Category Limits

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {D : Type u₂} [Category.{v₂} D]

namespace PresheafOfModules

variable {R : Cᵒᵖ ⥤ RingCat.{u}}
  {F : D ⥤ PresheafOfModules.{v} R}
  [forall X, Small.{v} ((F ⋙ evaluation R X) ⋙ forget _).sections]
  {c : Cone F}
  [HasLimitsOfShape D AddCommGrpCat.{v}]

/--
lemma `isSheaf_of_isLimit` / 引理 `isSheaf_of_isLimit`

English:
lemma isSheaf_of_isLimit
  given: (hc : IsLimit c) (hF : forall j, Presheaf.IsSheaf J (F.obj j).presheaf)
  proof: by
  let G : D ⥤ Sheaf J AddCommGrpCat.{v} :=
    { obj := fun j => ⟨(F.obj j).presheaf, hF j⟩
      map := fun φ => ⟨(PresheafOfModules.toPresheaf R).map (F.map φ)⟩ }
  exact Sheaf.isSheaf_of_isLimit G _ (isLimitOfPreserves (toPresheaf R) hc)

中文:
引理 isSheaf_of_isLimit
  条件: (hc : 是极限 c) (hF : 对任意 j, 预层.是层 J (F.obj j).presheaf)
  证明: by
  let G : D ⥤ Sheaf J AddCommGrpCat.{v} :=
    { obj := fun j => ⟨(F.obj j).presheaf, hF j⟩
      map := fun φ => ⟨(PresheafOfModules.toPresheaf R).map (F.map φ)⟩ }
  exact Sheaf.isSheaf_of_isLimit G _ (isLimitOfPreserves (toPresheaf R) hc)

Depends on / 依赖: AddCommGrpCat, F.map, F.obj, PresheafOfModules, PresheafOfModules.toPresheaf, Sheaf.isSheaf_of_isLimit, isLimitOfPreserves, isSheaf_of_isLimit, presheaf, toPresheaf
-/
lemma isSheaf_of_isLimit (hc : IsLimit c) (hF : forall j, Presheaf.IsSheaf J (F.obj j).presheaf) :
    Presheaf.IsSheaf J (c.pt.presheaf) := by
  let G : D ⥤ Sheaf J AddCommGrpCat.{v} :=
    { obj := fun j => ⟨(F.obj j).presheaf, hF j⟩
      map := fun φ => ⟨(PresheafOfModules.toPresheaf R).map (F.map φ)⟩ }
  exact Sheaf.isSheaf_of_isLimit G _ (isLimitOfPreserves (toPresheaf R) hc)

end PresheafOfModules

namespace SheafOfModules

variable {R : Sheaf J RingCat.{u}}

section Limits

variable (F : D ⥤ SheafOfModules.{v} R)
  [forall X, Small.{v} ((F ⋙ evaluation R X) ⋙ CategoryTheory.forget _).sections]
  [HasLimitsOfShape D AddCommGrpCat.{v}]

instance (X : Cᵒᵖ) : Small.{v} (((F ⋙ forget _) ⋙ PresheafOfModules.evaluation _ X) ⋙
    CategoryTheory.forget _).sections := by
  solve_by_elim

/--
Instance `createsLimit` / 实例 `createsLimit`

English:
instance createsLimit
  signature: : CreatesLimit F (forget _)
  body: createsLimitOfFullyFaithfulOfIso' (limit.isLimit (F ⋙ forget _))
    (mk (limit (F ⋙ forget _))
      (PresheafOfModules.isSheaf_of_isLimit (limit.isLimit (F ⋙ forget _))
        (fun j => (F.obj j).isSheaf))) (Iso.refl _)

中文:
实例 createsLimit
  签名: : 创造极限 F (forget _)
  定义体: createsLimitOfFullyFaithfulOfIso' (limit.isLimit (F ⋙ forget _))
    (mk (limit (F ⋙ forget _))
      (PresheafOfModules.isSheaf_of_isLimit (limit.isLimit (F ⋙ forget _))
        (fun j => (F.obj j).isSheaf))) (Iso.refl _)

Depends on / 依赖: F.obj, Iso.refl, PresheafOfModules, PresheafOfModules.isSheaf_of_isLimit, createsLimitOfFullyFaithfulOfIso, forget, isLimit, isSheaf, isSheaf_of_isLimit, limit.isLimit
-/
noncomputable instance createsLimit : CreatesLimit F (forget _) :=
  createsLimitOfFullyFaithfulOfIso' (limit.isLimit (F ⋙ forget _))
    (mk (limit (F ⋙ forget _))
      (PresheafOfModules.isSheaf_of_isLimit (limit.isLimit (F ⋙ forget _))
        (fun j => (F.obj j).isSheaf))) (Iso.refl _)

/--
Instance `hasLimit` / 实例 `hasLimit`

English:
instance hasLimit
  signature: : HasLimit F
  body: hasLimit_of_created F (forget _)

中文:
实例 hasLimit
  签名: : 有极限 F
  定义体: hasLimit_of_created F (forget _)

Depends on / 依赖: forget, hasLimit_of_created
-/
instance hasLimit : HasLimit F := hasLimit_of_created F (forget _)

/--
Instance `evaluationPreservesLimit` / 实例 `evaluationPreservesLimit`

English:
instance evaluationPreservesLimit
  signature: (X : Cᵒᵖ)
  body: by
  dsimp [evaluation]
  infer_instance

中文:
实例 evaluationPreservesLimit
  签名: (X : Cᵒᵖ)
  定义体: by
  dsimp [evaluation]
  infer_instance

Depends on / 依赖: evaluation, infer_instance
-/
noncomputable instance evaluationPreservesLimit (X : Cᵒᵖ) :
    PreservesLimit F (evaluation R X) := by
  dsimp [evaluation]
  infer_instance

end Limits

variable (R D)

section Small

variable [Small.{v} D]

/--
Instance `hasLimitsOfShape` / 实例 `hasLimitsOfShape`

English:
instance hasLimitsOfShape
  signature: : HasLimitsOfShape D (SheafOfModules.{v} R) where

中文:
实例 hasLimitsOfShape
  签名: : 有形状极限 D (模层.{v} R) where
-/
instance hasLimitsOfShape : HasLimitsOfShape D (SheafOfModules.{v} R) where

/--
Instance `evaluationPreservesLimitsOfShape` / 实例 `evaluationPreservesLimitsOfShape`

English:
instance evaluationPreservesLimitsOfShape
  signature: (X : Cᵒᵖ)

中文:
实例 evaluationPreservesLimitsOfShape
  签名: (X : Cᵒᵖ)
-/
noncomputable instance evaluationPreservesLimitsOfShape (X : Cᵒᵖ) :
    PreservesLimitsOfShape D (evaluation R X : SheafOfModules.{v} R ⥤ _) where

/--
Instance `forgetPreservesLimitsOfShape` / 实例 `forgetPreservesLimitsOfShape`

English:
instance forgetPreservesLimitsOfShape
  signature: :

中文:
实例 forgetPreservesLimitsOfShape
  签名: :
-/
noncomputable instance forgetPreservesLimitsOfShape :
    PreservesLimitsOfShape D (forget.{v} R) where

end Small

namespace Finite

/--
Instance `hasFiniteLimits` / 实例 `hasFiniteLimits`

English:
instance hasFiniteLimits
  signature: : HasFiniteLimits (SheafOfModules.{v} R)
  body: ⟨fun _ => inferInstance⟩

中文:
实例 hasFiniteLimits
  签名: : 有有限极限 (模层.{v} R)
  定义体: ⟨fun _ => inferInstance⟩
-/
instance hasFiniteLimits : HasFiniteLimits (SheafOfModules.{v} R) :=
  ⟨fun _ => inferInstance⟩

/--
Instance `evaluationPreservesFiniteLimits` / 实例 `evaluationPreservesFiniteLimits`

English:
instance evaluationPreservesFiniteLimits
  signature: (X : Cᵒᵖ)

中文:
实例 evaluationPreservesFiniteLimits
  签名: (X : Cᵒᵖ)
-/
noncomputable instance evaluationPreservesFiniteLimits (X : Cᵒᵖ) :
    PreservesFiniteLimits (evaluation.{v} R X) where

/--
Instance `forgetPreservesFiniteLimits` / 实例 `forgetPreservesFiniteLimits`

English:
instance forgetPreservesFiniteLimits
  signature: :

中文:
实例 forgetPreservesFiniteLimits
  签名: :

Depends on / 依赖: M.obj, Module, R.obj
-/
noncomputable instance forgetPreservesFiniteLimits :
    PreservesFiniteLimits (forget.{v} R) where

end Finite

/--
Instance `hasLimitsOfSize` / 实例 `hasLimitsOfSize`

English:
instance hasLimitsOfSize
  signature: : HasLimitsOfSize.{v₂, v} (SheafOfModules.{v} R) where

中文:
实例 hasLimitsOfSize
  签名: : 有LimitsOfSize.{v₂, v} (模层.{v} R) where
-/
instance hasLimitsOfSize : HasLimitsOfSize.{v₂, v} (SheafOfModules.{v} R) where

/--
Instance `evaluationPreservesLimitsOfSize` / 实例 `evaluationPreservesLimitsOfSize`

English:
instance evaluationPreservesLimitsOfSize
  signature: (X : Cᵒᵖ)

中文:
实例 evaluationPreservesLimitsOfSize
  签名: (X : Cᵒᵖ)
-/
noncomputable instance evaluationPreservesLimitsOfSize (X : Cᵒᵖ) :
    PreservesLimitsOfSize.{v₂, v} (evaluation R X : SheafOfModules.{v} R ⥤ _) where

/--
Instance `forgetPreservesLimitsOfSize` / 实例 `forgetPreservesLimitsOfSize`

English:
instance forgetPreservesLimitsOfSize
  signature: :

中文:
实例 forgetPreservesLimitsOfSize
  签名: :
-/
noncomputable instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v₂, v} (forget.{v} R) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: comp_preservesFiniteLimits (SheafOfModules.forget.{v} R) (PresheafOfModules.toPresheaf R.obj)

中文:
实例 :
  定义体: comp_preservesFiniteLimits (SheafOfModules.forget.{v} R) (PresheafOfModules.toPresheaf R.obj)

Depends on / 依赖: PresheafOfModules, PresheafOfModules.toPresheaf, R.obj, SheafOfModules, SheafOfModules.forget, comp_preservesFiniteLimits, forget, toPresheaf
-/
noncomputable instance :
     PreservesFiniteLimits (SheafOfModules.toSheaf.{v} R ⋙ sheafToPresheaf _ _) :=
  comp_preservesFiniteLimits (SheafOfModules.forget.{v} R) (PresheafOfModules.toPresheaf R.obj)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteLimits (SheafOfModules.toSheaf.{v} R)
  body: preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

中文:
实例 :
  签名: 保持FiniteLimits (模层.toSheaf.{v} R)
  定义体: preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

Depends on / 依赖: preservesFiniteLimits_of_reflects_of_preserves, sheafToPresheaf
-/
noncomputable instance : PreservesFiniteLimits (SheafOfModules.toSheaf.{v} R) :=
  preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

end SheafOfModules
