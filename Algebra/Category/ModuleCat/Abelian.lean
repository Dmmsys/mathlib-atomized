/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# The category of left R-modules is abelian.

Additionally, two linear maps are exact in the categorical sense iff `range f = ker g`.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe w v u

namespace ModuleCat

variable {R : Type u} [Ring R] {M N : ModuleCat.{v} R} (f : M ⟶ N)

/-- In the category of modules, every monomorphism is normal. -/
@[instance_reducible]
/-
**ModuleCat.normalMono** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：normalMono (hf : Mono f) : NormalMono f where Z
参数：hf : Mono f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.ker_eq_bot_of_mono`：ker_eq_bot_of_mono [Mono f] : LinearMap.ke
r f.hom = ⊥

--- 原说明 ---
In the category of modules, every monomorphism is normal.
-/
def normalMono (hf : Mono f) : NormalMono f where
  Z := of R (N ⧸ LinearMap.range f.hom)
  g := ofHom (LinearMap.range f.hom).mkQ
  w := hom_ext <| LinearMap.range_mkQ_comp _
  isLimit :=
    /- The following [invalid Lean code](https://github.com/leanprover-community/lean/issues/341)
        might help you understand what's going on here:
        ```
        calc
        M   ≃ₗ[R] f.ker.quotient  : (Submodule.quotEquivOfEqBot _ (ker_eq_bot_of_mono _)).symm
        ... ≃ₗ[R] f.range         : LinearMap.quotKerEquivRange f
        ... ≃ₗ[R] r.range.mkQ.ker : LinearEquiv.ofEq _ _ (Submodule.ker_mkQ _).symm
        ```
      -/
        IsKernel.isoKernel _ _ (kernelIsLimit _)
          (LinearEquiv.toModuleIso
            ((Submodule.quotEquivOfEqBot _ (ker_eq_bot_of_mono _)).symm ≪≫ₗ
              (LinearMap.quotKerEquivRange f.hom ≪≫ₗ
              LinearEquiv.ofEq _ _ (Submodule.ker_mkQ _).symm))) <| by ext; rfl

/-- In the category of modules, every epimorphism is normal. -/
@[instance_reducible]
/-
**ModuleCat.normalEpi** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：normalEpi (hf : Epi f) : NormalEpi f where W
参数：hf : Epi f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.range_eq_top_of_epi`：range_eq_top_of_epi [Epi f] : LinearMap.r
ange f.hom = ⊤

--- 原说明 ---
In the category of modules, every epimorphism is normal.
-/
def normalEpi (hf : Epi f) : NormalEpi f where
  W := of R (LinearMap.ker f.hom)
  g := ofHom (LinearMap.ker f.hom).subtype
  w := hom_ext <| LinearMap.comp_ker_subtype _
  isColimit :=
    /- The following invalid Lean code might help you understand what's going on here:
        ```
        calc f.ker.subtype.range.quotient
            ≃ₗ[R] f.ker.quotient : Submodule.quotEquivOfEq _ _ (Submodule.range_subtype _)
        ... ≃ₗ[R] f.range        : LinearMap.quotKerEquivRange f
        ... ≃ₗ[R] N              : LinearEquiv.ofTop _ (range_eq_top_of_epi _)
        ```
      -/
        IsCokernel.cokernelIso _ _ (cokernelIsColimit _)
          (LinearEquiv.toModuleIso
            (Submodule.quotEquivOfEq _ _ (Submodule.range_subtype _) ≪≫ₗ
                LinearMap.quotKerEquivRange f.hom ≪≫ₗ
              LinearEquiv.ofTop _ (range_eq_top_of_epi _))) <| by ext; rfl

/-- The category of R-modules is abelian. -/
/-
**ModuleCat.abelian** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
形式化陈述：abelian : Abelian (ModuleCat.{v} R) where has_cokernels
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.hasCokernels_moduleCat`：hasCokernels_moduleCat : HasCokernels 
(ModuleCat R)

--- 原说明 ---
The category of R-modules is abelian.
-/
instance abelian : Abelian (ModuleCat.{v} R) where
  has_cokernels := hasCokernels_moduleCat
  normalMonoOfMono f hf := ⟨normalMono f hf⟩
  normalEpiOfEpi f hf := ⟨normalEpi f hf⟩

section ReflectsLimits

/-- Add this instance to help Lean with universe levels. -/
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Add this instance to help Lean with universe levels.
-/
instance : HasLimitsOfSize.{v, v} (ModuleCat.{max v w} R) :=
  ModuleCat.hasLimitsOfSize.{v, v, max v w}

/- We need to put this in this weird spot because we need to know that the category of modules
    is balanced. -/
/-
**ModuleCat.forget_reflectsLimitsOfSize** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
形式化陈述：forget_reflectsLimitsOfSize : ReflectsLimitsOfSize.{v, v} (forget (ModuleC
at.{max v w} R))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimits_of_reflectsIsomorphisms`：reflectsLi
mits_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms] [HasLimitsOfSi
ze.{w', w} C] [PreservesLimitsOfSize.{w', w} G] : …
· 使用定理 `ModuleCat.instReflectsIsomorphismsForgetLinearMapIdCarrier`：∀ {R : Type 
u} [inst : Ring R], (CategoryTheory.forget (ModuleCat R)).ReflectsIsomorphisms
· 使用定理 `ModuleCat.instHasLimitsOfSize`：∀ {R : Type u} [inst : Ring R],   Categor
yTheory.Limits.HasLimitsOfSize.{v, v, max v w, max (max (v + 1) (w + 1)) u} (Mod
uleCat R)

--- 原说明 ---
We need to put this in this weird spot because we need to know that the category
 of modules
    is balanced.
-/
instance forget_reflectsLimitsOfSize :
    ReflectsLimitsOfSize.{v, v} (forget (ModuleCat.{max v w} R)) :=
  reflectsLimits_of_reflectsIsomorphisms
/-
**ModuleCat.forget** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget₂_reflectsLimitsOfSize :
    ReflectsLimitsOfSize.{v, v} (forget₂ (ModuleCat.{max v w} R) AddCommGrpCat.{max v w}) :=
  reflectsLimits_of_reflectsIsomorphisms
/-
**ModuleCat.forget_reflectsLimits** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
形式化陈述：forget_reflectsLimits : ReflectsLimits (forget (ModuleCat.{v} R))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget_reflectsLimits : ReflectsLimits (forget (ModuleCat.{v} R)) :=
  ModuleCat.forget_reflectsLimitsOfSize.{v, v}
/-
**ModuleCat.forget** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget₂_reflectsLimits : ReflectsLimits (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}) :=
  ModuleCat.forget₂_reflectsLimitsOfSize.{v, v}

end ReflectsLimits

end ModuleCat

