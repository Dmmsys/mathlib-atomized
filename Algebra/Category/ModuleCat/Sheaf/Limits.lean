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
  [∀ X, Small.{v} ((F ⋙ evaluation R X) ⋙ forget _).sections]
  {c : Cone F}
  [HasLimitsOfShape D AddCommGrpCat.{v}]

/-
**PresheafOfModules.isSheaf_of_isLimit** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModu
les`。
形式化陈述：isSheaf_of_isLimit (hc : IsLimit c) (hF : forall j, Presheaf.IsSheaf J (F.
obj j).presheaf) : Presheaf.IsSheaf J (c.pt.presheaf)
参数：hc : IsLimit c；hF : forall j, Presheaf.IsSheaf J (F.obj j).presheaf。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Sheaf.isSheaf_of_isLimit`：isSheaf_of_isLimit (F : K ⥤ She
af J D) (E : Cone (F ⋙ sheafToPresheaf J D)) (hE : IsLimit E) : Presheaf.IsSheaf
 J E.pt
-/
lemma isSheaf_of_isLimit (hc : IsLimit c) (hF : ∀ j, Presheaf.IsSheaf J (F.obj j).presheaf) :
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
  [∀ X, Small.{v} ((F ⋙ evaluation R X) ⋙ CategoryTheory.forget _).sections]
  [HasLimitsOfShape D AddCommGrpCat.{v}]

/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Cᵒᵖ) : Small.{v} (((F ⋙ forget _) ⋙ PresheafOfModules.evaluation _ X) ⋙
    CategoryTheory.forget _).sections := by
  solve_by_elim
/-
**SheafOfModules.createsLimit** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
形式化陈述：createsLimit : CreatesLimit F (forget _)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SheafOfModules.instFullPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
Forget`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : Categor
yTheory.GrothendieckTopology C}   (R : CategoryTheory.Sheaf J RingCa…
· 使用定理 `SheafOfModules.instFaithfulPresheafOfModulesObjFunctorOppositeRingCatIsS
heafForget`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : Cat
egoryTheory.GrothendieckTopology C}   (R : CategoryTheory.Sheaf J RingCa…
-/
noncomputable instance createsLimit : CreatesLimit F (forget _) :=
  createsLimitOfFullyFaithfulOfIso' (limit.isLimit (F ⋙ forget _))
    (mk (limit (F ⋙ forget _))
      (PresheafOfModules.isSheaf_of_isLimit (limit.isLimit (F ⋙ forget _))
        (fun j => (F.obj j).isSheaf))) (Iso.refl _)
/-
**SheafOfModules.hasLimit** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
形式化陈述：hasLimit : HasLimit F
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimit_of_created`：hasLimit_of_created (K : J ⥤ C) (F :
 C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLimit K F] : HasLimit K
· 使用定理 `SheafOfModules.instSmallElemForallObjCompModuleCatCarrierOppositeRingCat
ObjFunctorIsSheafPresheafOfModulesForgetEvaluationForgetLinearMapIdCarrierSectio
ns`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryThe
ory.GrothendieckTopology C} {D : Type u₂}   [inst_1 : CategoryTh…
-/
instance hasLimit : HasLimit F := hasLimit_of_created F (forget _)
/-
**SheafOfModules.evaluationPreservesLimit** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModu
les`。
形式化陈述：evaluationPreservesLimit (X : Cᵒᵖ) : PreservesLimit F (evaluation R X)
参数：X : Cᵒᵖ。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `SheafOfModules.instSmallElemForallObjCompModuleCatCarrierOppositeRingCat
ObjFunctorIsSheafPresheafOfModulesForgetEvaluationForgetLinearMapIdCarrierSectio
ns`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryThe
ory.GrothendieckTopology C} {D : Type u₂}   [inst_1 : CategoryTh…
-/
noncomputable instance evaluationPreservesLimit (X : Cᵒᵖ) :
    PreservesLimit F (evaluation R X) := by
  dsimp [evaluation]
  infer_instance

end Limits

variable (R D)

section Small

variable [Small.{v} D]

/-
**SheafOfModules.hasLimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `SheafOfModules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C} (D : Type u₂)   [inst_1 : CategoryTheory.Category.
{v₂, u₂} D] (R : CategoryTheory.Sheaf J RingCat) [Small.{v, u₂} D],   CategoryTh
eory.Limits.HasLimitsOfShape D (SheafOfModules R)
参数：D : Type u₂；R : CategoryTheory.Sheaf J RingCat；SheafOfModules R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `AddCommGrpCat.hasLimitsOfShape`：∀ {J : Type v} [inst : CategoryTheory.Ca
tegory.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimitsOfShape J Ad
dCommGrpCat
-/
instance hasLimitsOfShape : HasLimitsOfShape D (SheafOfModules.{v} R) where
/-
**SheafOfModules.evaluationPreservesLimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `She
afOfModules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C} (D : Type u₂)   [inst_1 : CategoryTheory.Category.
{v₂, u₂} D] (R : CategoryTheory.Sheaf J RingCat) [Small.{v, u₂} D] (X : Cᵒᵖ),   
CategoryTheory.Limits.PreservesLimitsOfShape D (SheafOfModules.evaluation R X)
参数：D : Type u₂；R : CategoryTheory.Sheaf J RingCat；X : Cᵒᵖ；SheafOfModules.evaluat
ion R X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `AddCommGrpCat.hasLimitsOfShape`：∀ {J : Type v} [inst : CategoryTheory.Ca
tegory.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimitsOfShape J Ad
dCommGrpCat
-/
noncomputable instance evaluationPreservesLimitsOfShape (X : Cᵒᵖ) :
    PreservesLimitsOfShape D (evaluation R X : SheafOfModules.{v} R ⥤ _) where
/-
**SheafOfModules.forgetPreservesLimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `SheafOf
Modules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C} (D : Type u₂)   [inst_1 : CategoryTheory.Category.
{v₂, u₂} D] (R : CategoryTheory.Sheaf J RingCat) [Small.{v, u₂} D],   CategoryTh
eory.Limits.PreservesLimitsOfShape D (SheafOfModules.forget R)
参数：D : Type u₂；R : CategoryTheory.Sheaf J RingCat；SheafOfModules.forget R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `AddCommGrpCat.hasLimitsOfShape`：∀ {J : Type v} [inst : CategoryTheory.Ca
tegory.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimitsOfShape J Ad
dCommGrpCat
· 使用定理 `SheafOfModules.instSmallElemForallObjCompModuleCatCarrierOppositeRingCat
ObjFunctorIsSheafPresheafOfModulesForgetEvaluationForgetLinearMapIdCarrierSectio
ns`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryThe
ory.GrothendieckTopology C} {D : Type u₂}   [inst_1 : CategoryTh…
-/
noncomputable instance forgetPreservesLimitsOfShape :
    PreservesLimitsOfShape D (forget.{v} R) where

end Small

namespace Finite

/-
**SheafOfModules.Finite.hasFiniteLimits** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModule
s.Finite`。
形式化陈述：hasFiniteLimits : HasFiniteLimits (SheafOfModules.{v} R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SheafOfModules.hasLimitsOfShape`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} (D : Type u₂)  
 [inst_1 : CategoryTh…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
instance hasFiniteLimits : HasFiniteLimits (SheafOfModules.{v} R) :=
  ⟨fun _ => inferInstance⟩
/-
**SheafOfModules.Finite.evaluationPreservesFiniteLimits** 是 Mathlib 中的一个定理，位于命名空
间 `SheafOfModules.Finite`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C}   (R : CategoryTheory.Sheaf J RingCat) (X : Cᵒᵖ), 
  CategoryTheory.Limits.PreservesFiniteLimits (SheafOfModules.evaluation R X)
参数：R : CategoryTheory.Sheaf J RingCat；X : Cᵒᵖ；SheafOfModules.evaluation R X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SheafOfModules.evaluationPreservesLimitsOfShape`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C}
 (D : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
noncomputable instance evaluationPreservesFiniteLimits (X : Cᵒᵖ) :
    PreservesFiniteLimits (evaluation.{v} R X) where
/-
**SheafOfModules.Finite.forgetPreservesFiniteLimits** 是 Mathlib 中的一个定理，位于命名空间 `S
heafOfModules.Finite`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C}   (R : CategoryTheory.Sheaf J RingCat), CategoryTh
eory.Limits.PreservesFiniteLimits (SheafOfModules.forget R)
参数：R : CategoryTheory.Sheaf J RingCat；SheafOfModules.forget R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SheafOfModules.forgetPreservesLimitsOfShape`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} (D 
: Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
noncomputable instance forgetPreservesFiniteLimits :
    PreservesFiniteLimits (forget.{v} R) where

end Finite

/-
**SheafOfModules.hasLimitsOfSize** 是 Mathlib 中的一个定理，位于命名空间 `SheafOfModules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C}   (R : CategoryTheory.Sheaf J RingCat),   Category
Theory.Limits.HasLimitsOfSize.{v₂, v, max u₁ v, max (max (max (v + 1) u) u₁) v₁}
 (SheafOfModules R)
参数：R : CategoryTheory.Sheaf J RingCat；max (max (v + 1) u) u₁；SheafOfModules R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SheafOfModules.hasLimitsOfShape`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} (D : Type u₂)  
 [inst_1 : CategoryTh…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
instance hasLimitsOfSize : HasLimitsOfSize.{v₂, v} (SheafOfModules.{v} R) where
/-
**SheafOfModules.evaluationPreservesLimitsOfSize** 是 Mathlib 中的一个定理，位于命名空间 `Shea
fOfModules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C}   (R : CategoryTheory.Sheaf J RingCat) (X : Cᵒᵖ), 
  CategoryTheory.Limits.PreservesLimitsOfSize.{v₂, v, max u₁ v, v, max (max (max
 u u₁) (v + 1)) v₁, max u (v + 1)}     (SheafOfModules.evaluation R X)
参数：R : CategoryTheory.Sheaf J RingCat；X : Cᵒᵖ；max (max u u₁) (v + 1)；v + 1；Sheaf
OfModules.evaluation R X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SheafOfModules.evaluationPreservesLimitsOfShape`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C}
 (D : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
noncomputable instance evaluationPreservesLimitsOfSize (X : Cᵒᵖ) :
    PreservesLimitsOfSize.{v₂, v} (evaluation R X : SheafOfModules.{v} R ⥤ _) where
/-
**SheafOfModules.forgetPreservesLimitsOfSize** 是 Mathlib 中的一个定理，位于命名空间 `SheafOfM
odules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C}   (R : CategoryTheory.Sheaf J RingCat),   Category
Theory.Limits.PreservesLimitsOfSize.{v₂, v, max u₁ v, max u₁ v, max (max (max u 
u₁) (v + 1)) v₁,       max (max (max u u₁) (v + 1)) v₁}     (SheafOfModules.forg
et R)
参数：R : CategoryTheory.Sheaf J RingCat；max (max u u₁) (v + 1)；max (max u u₁) (v +
 1)；SheafOfModules.forget R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SheafOfModules.forgetPreservesLimitsOfShape`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} (D 
: Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
noncomputable instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v₂, v} (forget.{v} R) where
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance :
     PreservesFiniteLimits (SheafOfModules.toSheaf.{v} R ⋙ sheafToPresheaf _ _) :=
  comp_preservesFiniteLimits (SheafOfModules.forget.{v} R) (PresheafOfModules.toPresheaf R.obj)
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesFiniteLimits (SheafOfModules.toSheaf.{v} R) :=
  preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

end SheafOfModules

