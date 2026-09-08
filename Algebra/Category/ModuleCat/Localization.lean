/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.RingTheory.Localization.Module

/-!

# Localized Module in ModuleCat

For a ring `R` satisfying `[Small.{v} R]` and a submonoid `S` of `R`,
this file defines an exact functor `ModuleCat.{v} R ⥤ ModuleCat.{v} (Localization S)`,
see `ModuleCat.localizedModuleFunctor`.

-/

@[expose] public section

universe v u

variable (R : Type u) [CommRing R]

open CategoryTheory

local instance [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M] (S : Submonoid R) :
    Small.{v} (LocalizedModule S M) :=
  small_of_surjective (IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S M))

variable {R}

namespace ModuleCat

/-- Shrink of `LocalizedModule S M` in category which `M` belongs. -/
/-
**ModuleCat.localizedModule** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：localizedModule [Small.{v} R] (M : ModuleCat.{v} R) (S : Submonoid R) : Mo
duleCat.{v} (Localization S)
参数：M : ModuleCat.{v} R；S : Submonoid R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Shrink of `LocalizedModule S M` in category which `M` belongs.
-/
noncomputable def localizedModule [Small.{v} R] (M : ModuleCat.{v} R) (S : Submonoid R) :
    ModuleCat.{v} (Localization S) :=
  ModuleCat.of.{v} _ (Shrink.{v} (LocalizedModule S M))

/-- The `R` module structure on `M.localizedModule S` given by the
`R` module structure on `Shrink.{v} (LocalizedModule S M)` -/
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R` module structure on `M.localizedModule S` given by the
`R` module structure on `Shrink.{v} (LocalizedModule S M)`
-/
noncomputable instance [Small.{v} R] (M : ModuleCat.{v} R) (S : Submonoid R) :
    Module R (M.localizedModule S) :=
  inferInstanceAs (Module R (Shrink.{v} (LocalizedModule S M)))
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Small.{v} R] (M : ModuleCat.{v} R) (S : Submonoid R) :
    IsScalarTower R (Localization S) (M.localizedModule S) :=
  (equivShrink (LocalizedModule S M)).symm.isScalarTower R (Localization S)

/-- The linear map `M →ₗ[R] (M.localizedModule S)` which
exhibits `M.localizedModule S` as a localized module of `M`. -/
/-
**ModuleCat.localizedModuleMkLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：localizedModuleMkLinearMap [Small.{v} R] (M : ModuleCat.{v} R) (S : Submon
oid R) : M ->ₗ[R] (M.localizedModule S)
参数：M : ModuleCat.{v} R；S : Submonoid R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map `M →ₗ[R] (M.localizedModule S)` which
exhibits `M.localizedModule S` as a localized module of `M`.
-/
noncomputable def localizedModuleMkLinearMap [Small.{v} R] (M : ModuleCat.{v} R)
    (S : Submonoid R) : M →ₗ[R] (M.localizedModule S) :=
  (Shrink.linearEquiv.{v} R _).symm.toLinearMap.comp (LocalizedModule.mkLinearMap S M)

set_option backward.isDefEq.respectTransparency false in
/-
**ModuleCat.localizedModule_isLocalizedModule** 是 Mathlib 中的一个实例，位于命名空间 `ModuleC
at`。
形式化陈述：localizedModule_isLocalizedModule [Small.{v} R] (M : ModuleCat.{v} R) (S :
 Submonoid R) : IsLocalizedModule S (M.localizedModuleMkLinearMap S)
参数：M : ModuleCat.{v} R；S : Submonoid R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance localizedModule_isLocalizedModule [Small.{v} R] (M : ModuleCat.{v} R)
    (S : Submonoid R) : IsLocalizedModule S (M.localizedModuleMkLinearMap S) := by
  dsimp only [localizedModuleMkLinearMap]
  infer_instance

/-- `IsLocalizedModule.mapExtendScalars` as a morphism in `ModuleCat`. -/
@[simps!]
/-
**ModuleCat.localizedModuleMap** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：localizedModuleMap [Small.{v} R] {M N : ModuleCat.{v} R} (S : Submonoid R)
 (f : M ⟶ N) : (M.localizedModule S) ⟶ (N.localizedModule S)
参数：S : Submonoid R；f : M ⟶ N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.instIsScalarTowerLocalizationCarrierLocalizedModule`：∀ {R : Ty
pe u} [inst : CommRing R] [inst_1 : Small.{v, u} R] (M : ModuleCat R) (S : Submo
noid R),   IsScalarTower R (Localization S) ↑(M.loc…

--- 原说明 ---
`IsLocalizedModule.mapExtendScalars` as a morphism in `ModuleCat`.
-/
noncomputable def localizedModuleMap [Small.{v} R] {M N : ModuleCat.{v} R}
    (S : Submonoid R) (f : M ⟶ N) : (M.localizedModule S) ⟶ (N.localizedModule S) :=
  ModuleCat.ofHom.{v} <| IsLocalizedModule.mapExtendScalars S (M.localizedModuleMkLinearMap S)
    (N.localizedModuleMkLinearMap S) (Localization S) f.hom

/-- The functor `ModuleCat.{v} R ⥤ ModuleCat.{v} (Localization S)` sending
`M` to `M.localizedModule S` and `f : M1 ⟶ M2` to
`IsLocalizedModule.mapExtendScalars S _ _ (Localization S) f.hom`. -/
@[simps]
/-
**ModuleCat.localizedModuleFunctor** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：localizedModuleFunctor [Small.{v} R] (S : Submonoid R) : ModuleCat.{v} R ⥤
 ModuleCat.{v} (Localization S) where obj M
参数：S : Submonoid R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `ModuleCat.{v} R ⥤ ModuleCat.{v} (Localization S)` sending
`M` to `M.localizedModule S` and `f : M1 ⟶ M2` to
`IsLocalizedModule.mapExtendScalars S _ _ (Localization S) f.hom`.
-/
noncomputable def localizedModuleFunctor [Small.{v} R] (S : Submonoid R) :
    ModuleCat.{v} R ⥤ ModuleCat.{v} (Localization S) where
  obj M := M.localizedModule S
  map := ModuleCat.localizedModuleMap S
  map_comp {X Y Z} f g := by
    ext
    simp [IsLocalizedModule.map_comp' S _ (Y.localizedModuleMkLinearMap S)]
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Small.{v} R] (S : Submonoid R) : (ModuleCat.localizedModuleFunctor S).Additive where
/-
**ModuleCat.localizedModuleFunctor_map_exact** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCa
t`。
形式化陈述：localizedModuleFunctor_map_exact [Small.{v} R] (S : Submonoid R) (T : Shor
tComplex (ModuleCat.{v} R)) (h : T.Exact) : (T.map (ModuleCat.localizedModuleFun
ctor S)).Exact
参数：S : Submonoid R；T : ShortComplex (ModuleCat.{v} R)；h : T.Exact。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `ModuleCat.instAdditiveLocalizationLocalizedModuleFunctor`：∀ {R : Type u}
 [inst : CommRing R] [inst_1 : Small.{v, u} R] (S : Submonoid R),   (ModuleCat.l
ocalizedModuleFunctor S).Additive
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exac
t`：∀ {R : Type u} [inst : Ring R] (S : CategoryTheory.ShortComplex (ModuleCat R)
),   S.Exact ↔ Function.Exact ⇑(CategoryTheory.ConcreteCategory…
· 使用定理 `IsLocalizedModule.map_exact`：IsLocalizedModule.map_exact (g : M₀ ->ₗ[R] 
M₁) (h : M₁ ->ₗ[R] M₂) (ex : Function.Exact g h) : Function.Exact (map S f₀ f₁ g
) (map S f₁ f₂ h)
-/
lemma localizedModuleFunctor_map_exact [Small.{v} R] (S : Submonoid R)
    (T : ShortComplex (ModuleCat.{v} R)) (h : T.Exact) :
    (T.map (ModuleCat.localizedModuleFunctor S)).Exact := by
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact IsLocalizedModule.map_exact S (T.X₁.localizedModuleMkLinearMap S)
    (T.X₂.localizedModuleMkLinearMap S) (T.X₃.localizedModuleMkLinearMap S) _ _ h
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Small.{v} R] (S : Submonoid R) :
    Limits.PreservesFiniteLimits (ModuleCat.localizedModuleFunctor.{v} S) := by
  have := ((Functor.exact_tfae _).out 1 3).mp (ModuleCat.localizedModuleFunctor_map_exact S)
  exact this.1
/-
**ModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Small.{v} R] (S : Submonoid R) :
    Limits.PreservesFiniteColimits (ModuleCat.localizedModuleFunctor.{v} S) := by
  have := ((Functor.exact_tfae _).out 1 3).mp (ModuleCat.localizedModuleFunctor_map_exact S)
  exact this.2
/-
**ModuleCat.isIso_of_isLocalizedModule_comp** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat
`。
形式化陈述：isIso_of_isLocalizedModule_comp {S : Submonoid R} {M₁ M₂ M₃ : ModuleCat R}
 {f₁ : M₁ ⟶ M₂} {f₂ : M₂ ⟶ M₃} (h₁ : IsLocalizedModule S f₁.hom) (h₂ : IsLocaliz
edModule S (f₁ ≫ f₂).hom) : IsIso f₂
参数：h₁ : IsLocalizedModule S f₁.hom；h₂ : IsLocalizedModule S (f₁ ≫ f₂).hom。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsLocalizedModule.linearEquiv_of_isLocalizedModule_comp`：linearEquiv_of_
isLocalizedModule_comp (g : M' ->ₗ[R] M'') [IsLocalizedModule S (g ∘ₗ f)] : line
arEquiv S f (g ∘ₗ f) = g
· 使用定理 `LinearEquiv.bijective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `ModuleCat.instReflectsIsomorphismsForgetLinearMapIdCarrier`：∀ {R : Type 
u} [inst : Ring R], (CategoryTheory.forget (ModuleCat R)).ReflectsIsomorphisms
-/
lemma isIso_of_isLocalizedModule_comp {S : Submonoid R} {M₁ M₂ M₃ : ModuleCat R} {f₁ : M₁ ⟶ M₂}
    {f₂ : M₂ ⟶ M₃} (h₁ : IsLocalizedModule S f₁.hom) (h₂ : IsLocalizedModule S (f₁ ≫ f₂).hom) :
    IsIso f₂ := by
  have : Function.Bijective f₂.hom := by
    rw [← IsLocalizedModule.linearEquiv_of_isLocalizedModule_comp S f₁.hom f₂.hom]
    exact (IsLocalizedModule.linearEquiv ..).bijective
  simpa [ConcreteCategory.isIso_iff_bijective]

end ModuleCat

