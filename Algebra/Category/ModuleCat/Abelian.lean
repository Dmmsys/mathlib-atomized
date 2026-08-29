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
/--
Definition of `normalMono` / `normalMono` 的定义

English:
definition normalMono
  signature: (hf : Mono f)
  body: of R (N ⧸ LinearMap.range f.hom)
  g := ofHom (LinearMap.range f.hom).mkQ
w := hom_ext LinearMap.range_mkQ_comp _
  isLimit :=
    /- The following [invalid Lean code](https://github.com/leanprover-community/lean/issues/341)
        might help you understand what's going on here:
        ```
        calc
        M ≃ₗ[R] f.ker.quotient : (Submodule.quotEquivOfEqBot _ (ker_eq_bot_of_mono _)).symm
        ... ≃ₗ[R] f.range : LinearMap.quotKerEquivRange f
        ... ≃ₗ[R] r.range.mkQ.ker : LinearEquiv.ofEq _ _ (Submodule.ker_mkQ _).symm
        ```
      -/
        IsKernel.isoKernel _ _ (kernelIsLimit _)
          (LinearEquiv.toModuleIso
            ((Submodule.quotEquivOfEqBot _ (ker_eq_bot_of_mono _)).symm ≪≫ₗ
              (LinearMap.quotKerEquivRange f.hom ≪≫ₗ
              LinearEquiv.ofEq _ _ (Submodule.ker_mkQ _).symm))) <| by ext; rfl

中文:
定义 normalMono
  签名: (hf : 单态射 f)
  定义体: of R (N ⧸ LinearMap.range f.hom)
  g := ofHom (LinearMap.range f.hom).mkQ
w := hom_ext LinearMap.range_mkQ_comp _
  isLimit :=
    /- The following [invalid Lean code](https://github.com/leanprover-community/lean/issues/341)
        might help you understand what's going on here:
        ```
        calc
        M ≃ₗ[R] f.ker.quotient : (Submodule.quotEquivOfEqBot _ (ker_eq_bot_of_mono _)).symm
        ... ≃ₗ[R] f.range : LinearMap.quotKerEquivRange f
        ... ≃ₗ[R] r.range.mkQ.ker : LinearEquiv.ofEq _ _ (Submodule.ker_mkQ _).symm
        ```
      -/
        IsKernel.isoKernel _ _ (kernelIsLimit _)
          (LinearEquiv.toModuleIso
            ((Submodule.quotEquivOfEqBot _ (ker_eq_bot_of_mono _)).symm ≪≫ₗ
              (LinearMap.quotKerEquivRange f.hom ≪≫ₗ
              LinearEquiv.ofEq _ _ (Submodule.ker_mkQ _).symm))) <| by ext; rfl

Depends on / 依赖: LinearMap, LinearMap.range, f.hom
-/
def normalMono (hf : Mono f) : NormalMono f where
  Z := of R (N ⧸ LinearMap.range f.hom)
  g := ofHom (LinearMap.range f.hom).mkQ
w := hom_ext LinearMap.range_mkQ_comp _
  isLimit :=
    /- The following [invalid Lean code](https://github.com/leanprover-community/lean/issues/341)
        might help you understand what's going on here:
        ```
        calc
        M ≃ₗ[R] f.ker.quotient : (Submodule.quotEquivOfEqBot _ (ker_eq_bot_of_mono _)).symm
        ... ≃ₗ[R] f.range : LinearMap.quotKerEquivRange f
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
/--
Definition of `normalEpi` / `normalEpi` 的定义

English:
definition normalEpi
  signature: (hf : Epi f)
  body: of R (LinearMap.ker f.hom)
  g := ofHom (LinearMap.ker f.hom).subtype
w := hom_ext LinearMap.comp_ker_subtype _
  isColimit :=
    /- The following invalid Lean code might help you understand what's going on here:
        ```
        calc f.ker.subtype.range.quotient
            ≃ₗ[R] f.ker.quotient : Submodule.quotEquivOfEq _ _ (Submodule.range_subtype _)
        ... ≃ₗ[R] f.range : LinearMap.quotKerEquivRange f
        ... ≃ₗ[R] N : LinearEquiv.ofTop _ (range_eq_top_of_epi _)
        ```
      -/
        IsCokernel.cokernelIso _ _ (cokernelIsColimit _)
          (LinearEquiv.toModuleIso
            (Submodule.quotEquivOfEq _ _ (Submodule.range_subtype _) ≪≫ₗ
                LinearMap.quotKerEquivRange f.hom ≪≫ₗ
              LinearEquiv.ofTop _ (range_eq_top_of_epi _))) <| by ext; rfl

中文:
定义 normalEpi
  签名: (hf : 满态射 f)
  定义体: of R (LinearMap.ker f.hom)
  g := ofHom (LinearMap.ker f.hom).subtype
w := hom_ext LinearMap.comp_ker_subtype _
  isColimit :=
    /- The following invalid Lean code might help you understand what's going on here:
        ```
        calc f.ker.subtype.range.quotient
            ≃ₗ[R] f.ker.quotient : Submodule.quotEquivOfEq _ _ (Submodule.range_subtype _)
        ... ≃ₗ[R] f.range : LinearMap.quotKerEquivRange f
        ... ≃ₗ[R] N : LinearEquiv.ofTop _ (range_eq_top_of_epi _)
        ```
      -/
        IsCokernel.cokernelIso _ _ (cokernelIsColimit _)
          (LinearEquiv.toModuleIso
            (Submodule.quotEquivOfEq _ _ (Submodule.range_subtype _) ≪≫ₗ
                LinearMap.quotKerEquivRange f.hom ≪≫ₗ
              LinearEquiv.ofTop _ (range_eq_top_of_epi _))) <| by ext; rfl

Depends on / 依赖: LinearMap, LinearMap.ker, f.hom
-/
def normalEpi (hf : Epi f) : NormalEpi f where
  W := of R (LinearMap.ker f.hom)
  g := ofHom (LinearMap.ker f.hom).subtype
w := hom_ext LinearMap.comp_ker_subtype _
  isColimit :=
    /- The following invalid Lean code might help you understand what's going on here:
        ```
        calc f.ker.subtype.range.quotient
            ≃ₗ[R] f.ker.quotient : Submodule.quotEquivOfEq _ _ (Submodule.range_subtype _)
        ... ≃ₗ[R] f.range : LinearMap.quotKerEquivRange f
        ... ≃ₗ[R] N : LinearEquiv.ofTop _ (range_eq_top_of_epi _)
        ```
      -/
        IsCokernel.cokernelIso _ _ (cokernelIsColimit _)
          (LinearEquiv.toModuleIso
            (Submodule.quotEquivOfEq _ _ (Submodule.range_subtype _) ≪≫ₗ
                LinearMap.quotKerEquivRange f.hom ≪≫ₗ
              LinearEquiv.ofTop _ (range_eq_top_of_epi _))) <| by ext; rfl

/--
Instance `abelian` / 实例 `abelian`

English:
instance abelian
  signature: : Abelian (ModuleCat.{v} R) where
  body: hasCokernels_moduleCat
  normalMonoOfMono f hf := ⟨normalMono f hf⟩
  normalEpiOfEpi f hf := ⟨normalEpi f hf⟩

中文:
实例 abelian
  签名: : 交换 (模范畴.{v} R) where
  定义体: hasCokernels_moduleCat
  normalMonoOfMono f hf := ⟨normalMono f hf⟩
  normalEpiOfEpi f hf := ⟨normalEpi f hf⟩

Depends on / 依赖: hasCokernels_moduleCat
-/
instance abelian : Abelian (ModuleCat.{v} R) where
  has_cokernels := hasCokernels_moduleCat
  normalMonoOfMono f hf := ⟨normalMono f hf⟩
  normalEpiOfEpi f hf := ⟨normalEpi f hf⟩

section ReflectsLimits

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLimitsOfSize.{v, v} (ModuleCat.{max v w} R)
  body: ModuleCat.hasLimitsOfSize.{v, v, max v w}

中文:
实例 :
  签名: 有LimitsOfSize.{v, v} (模范畴.{最大值 v w} R)
  定义体: ModuleCat.hasLimitsOfSize.{v, v, max v w}

Depends on / 依赖: ModuleCat, ModuleCat.hasLimitsOfSize, hasLimitsOfSize
-/
instance : HasLimitsOfSize.{v, v} (ModuleCat.{max v w} R) :=
  ModuleCat.hasLimitsOfSize.{v, v, max v w}

/--
Instance `forget_reflectsLimitsOfSize` / 实例 `forget_reflectsLimitsOfSize`

English:
instance forget_reflectsLimitsOfSize
  signature: :
  body: reflectsLimits_of_reflectsIsomorphisms

中文:
实例 forget_reflectsLimitsOfSize
  签名: :
  定义体: reflectsLimits_of_reflectsIsomorphisms

Depends on / 依赖: reflectsLimits_of_reflectsIsomorphisms
-/
instance forget_reflectsLimitsOfSize :
    ReflectsLimitsOfSize.{v, v} (forget (ModuleCat.{max v w} R)) :=
  reflectsLimits_of_reflectsIsomorphisms

/--
Instance `forget₂_reflectsLimitsOfSize` / 实例 `forget₂_reflectsLimitsOfSize`

English:
instance forget₂_reflectsLimitsOfSize
  signature: :
  body: reflectsLimits_of_reflectsIsomorphisms

中文:
实例 forget₂_reflectsLimitsOfSize
  签名: :
  定义体: reflectsLimits_of_reflectsIsomorphisms

Depends on / 依赖: reflectsLimits_of_reflectsIsomorphisms
-/
instance forget₂_reflectsLimitsOfSize :
    ReflectsLimitsOfSize.{v, v} (forget₂ (ModuleCat.{max v w} R) AddCommGrpCat.{max v w}) :=
  reflectsLimits_of_reflectsIsomorphisms

/--
Instance `forget_reflectsLimits` / 实例 `forget_reflectsLimits`

English:
instance forget_reflectsLimits
  signature: : ReflectsLimits (forget (ModuleCat.{v} R))
  body: ModuleCat.forget_reflectsLimitsOfSize.{v, v}

中文:
实例 forget_reflectsLimits
  签名: : ReflectsLimits (forget (模范畴.{v} R))
  定义体: ModuleCat.forget_reflectsLimitsOfSize.{v, v}

Depends on / 依赖: ModuleCat, ModuleCat.forget_reflectsLimitsOfSize, forget_reflectsLimitsOfSize
-/
instance forget_reflectsLimits : ReflectsLimits (forget (ModuleCat.{v} R)) :=
  ModuleCat.forget_reflectsLimitsOfSize.{v, v}

/--
Instance `forget₂_reflectsLimits` / 实例 `forget₂_reflectsLimits`

English:
instance forget₂_reflectsLimits
  signature: : ReflectsLimits (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})
  body: ModuleCat.forget₂_reflectsLimitsOfSize.{v, v}

中文:
实例 forget₂_reflectsLimits
  签名: : ReflectsLimits (forget₂ (模范畴.{v} R) 加法交换群范畴.{v})
  定义体: ModuleCat.forget₂_reflectsLimitsOfSize.{v, v}

Depends on / 依赖: ModuleCat, ModuleCat.forget
-/
instance forget₂_reflectsLimits : ReflectsLimits (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}) :=
  ModuleCat.forget₂_reflectsLimitsOfSize.{v, v}

end ReflectsLimits

end ModuleCat
