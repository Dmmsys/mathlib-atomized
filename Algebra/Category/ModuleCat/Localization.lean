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

/--
Definition of `localizedModule` / `localizedModule` 的定义

English:
definition localizedModule
  signature: [Small.{v} R] (M : ModuleCat.{v} R) (S : Submonoid R)
  body: ModuleCat.of.{v} _ (Shrink.{v} (LocalizedModule S M))

中文:
定义 localizedModule
  签名: [Small.{v} R] (M : 模范畴.{v} R) (S : 子幺半群 R)
  定义体: ModuleCat.of.{v} _ (Shrink.{v} (LocalizedModule S M))

Depends on / 依赖: LocalizedModule, ModuleCat, ModuleCat.of, Shrink
-/
noncomputable def localizedModule [Small.{v} R] (M : ModuleCat.{v} R) (S : Submonoid R) :
    ModuleCat.{v} (Localization S) :=
  ModuleCat.of.{v} _ (Shrink.{v} (LocalizedModule S M))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{v}
  signature: R] (M
  body: inferInstanceAs (Module R (Shrink.{v} (LocalizedModule S M)))

中文:
实例 [Small.{v}
  签名: R] (M
  定义体: inferInstanceAs (Module R (Shrink.{v} (LocalizedModule S M)))

Depends on / 依赖: LocalizedModule, Module, Shrink
-/
noncomputable instance [Small.{v} R] (M : ModuleCat.{v} R) (S : Submonoid R) :
    Module R (M.localizedModule S) :=
  inferInstanceAs (Module R (Shrink.{v} (LocalizedModule S M)))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{v}
  signature: R] (M
  body: (equivShrink (LocalizedModule S M)).symm.isScalarTower R (Localization S)

中文:
实例 [Small.{v}
  签名: R] (M
  定义体: (equivShrink (LocalizedModule S M)).symm.isScalarTower R (Localization S)

Depends on / 依赖: Localization, LocalizedModule, equivShrink, isScalarTower, symm.isScalarTower
-/
instance [Small.{v} R] (M : ModuleCat.{v} R) (S : Submonoid R) :
    IsScalarTower R (Localization S) (M.localizedModule S) :=
  (equivShrink (LocalizedModule S M)).symm.isScalarTower R (Localization S)

/--
Definition of `localizedModuleMkLinearMap` / `localizedModuleMkLinearMap` 的定义

English:
definition localizedModuleMkLinearMap
  signature: [Small.{v} R] (M : ModuleCat.{v} R)
  body: (Shrink.linearEquiv.{v} R _).symm.toLinearMap.comp (LocalizedModule.mkLinearMap S M)

中文:
定义 localizedModuleMkLinearMap
  签名: [Small.{v} R] (M : 模范畴.{v} R)
  定义体: (Shrink.linearEquiv.{v} R _).symm.toLinearMap.comp (LocalizedModule.mkLinearMap S M)

Depends on / 依赖: LocalizedModule, LocalizedModule.mkLinearMap, Shrink, Shrink.linearEquiv, linearEquiv, mkLinearMap, symm.toLinearMap.comp, toLinearMap
-/
noncomputable def localizedModuleMkLinearMap [Small.{v} R] (M : ModuleCat.{v} R)
    (S : Submonoid R) : M ->ₗ[R] (M.localizedModule S) :=
  (Shrink.linearEquiv.{v} R _).symm.toLinearMap.comp (LocalizedModule.mkLinearMap S M)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `localizedModule_isLocalizedModule` / 实例 `localizedModule_isLocalizedModule`

English:
instance localizedModule_isLocalizedModule
  signature: [Small.{v} R] (M : ModuleCat.{v} R)
  body: by
  dsimp only [localizedModuleMkLinearMap]
  infer_instance

中文:
实例 localizedModule_isLocalizedModule
  签名: [Small.{v} R] (M : 模范畴.{v} R)
  定义体: by
  dsimp only [localizedModuleMkLinearMap]
  infer_instance

Depends on / 依赖: infer_instance, localizedModuleMkLinearMap
-/
instance localizedModule_isLocalizedModule [Small.{v} R] (M : ModuleCat.{v} R)
    (S : Submonoid R) : IsLocalizedModule S (M.localizedModuleMkLinearMap S) := by
  dsimp only [localizedModuleMkLinearMap]
  infer_instance

/-- `IsLocalizedModule.mapExtendScalars` as a morphism in `ModuleCat`. -/
@[simps!]
/--
Definition of `localizedModuleMap` / `localizedModuleMap` 的定义

English:
definition localizedModuleMap
  signature: [Small.{v} R] {M N : ModuleCat.{v} R}
  body: ModuleCat.ofHom.{v} IsLocalizedModule.mapExtendScalars S (M.localizedModuleMkLinearMap S)
    (N.localizedModuleMkLinearMap S) (Localization S) f.hom

中文:
定义 localizedModuleMap
  签名: [Small.{v} R] {M N : 模范畴.{v} R}
  定义体: ModuleCat.ofHom.{v} IsLocalizedModule.mapExtendScalars S (M.localizedModuleMkLinearMap S)
    (N.localizedModuleMkLinearMap S) (Localization S) f.hom

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.mapExtendScalars, Localization, M.localizedModuleMkLinearMap, ModuleCat, ModuleCat.ofHom, N.localizedModuleMkLinearMap, f.hom, localizedModuleMkLinearMap, mapExtendScalars
-/
noncomputable def localizedModuleMap [Small.{v} R] {M N : ModuleCat.{v} R}
    (S : Submonoid R) (f : M ⟶ N) : (M.localizedModule S) ⟶ (N.localizedModule S) :=
ModuleCat.ofHom.{v} IsLocalizedModule.mapExtendScalars S (M.localizedModuleMkLinearMap S)
    (N.localizedModuleMkLinearMap S) (Localization S) f.hom

/-- The functor `ModuleCat.{v} R ⥤ ModuleCat.{v} (Localization S)` sending
`M` to `M.localizedModule S` and `f : M1 ⟶ M2` to
`IsLocalizedModule.mapExtendScalars S _ _ (Localization S) f.hom`. -/
@[simps]
/--
Definition of `localizedModuleFunctor` / `localizedModuleFunctor` 的定义

English:
definition localizedModuleFunctor
  signature: [Small.{v} R] (S : Submonoid R)
  body: M.localizedModule S
  map := ModuleCat.localizedModuleMap S
  map_comp {X Y Z} f g := by
    ext
    simp [IsLocalizedModule.map_comp' S _ (Y.localizedModuleMkLinearMap S)]

中文:
定义 localizedModuleFunctor
  签名: [Small.{v} R] (S : 子幺半群 R)
  定义体: M.localizedModule S
  map := ModuleCat.localizedModuleMap S
  map_comp {X Y Z} f g := by
    ext
    simp [IsLocalizedModule.map_comp' S _ (Y.localizedModuleMkLinearMap S)]

Depends on / 依赖: M.localizedModule, localizedModule
-/
noncomputable def localizedModuleFunctor [Small.{v} R] (S : Submonoid R) :
    ModuleCat.{v} R ⥤ ModuleCat.{v} (Localization S) where
  obj M := M.localizedModule S
  map := ModuleCat.localizedModuleMap S
  map_comp {X Y Z} f g := by
    ext
    simp [IsLocalizedModule.map_comp' S _ (Y.localizedModuleMkLinearMap S)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{v}
  signature: R] (S

中文:
实例 [Small.{v}
  签名: R] (S
-/
instance [Small.{v} R] (S : Submonoid R) : (ModuleCat.localizedModuleFunctor S).Additive where

/--
lemma `localizedModuleFunctor_map_exact` / 引理 `localizedModuleFunctor_map_exact`

English:
lemma localizedModuleFunctor_map_exact
  statement: [Small.{v} R] (S : Submonoid R)
  proof: by
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact IsLocalizedModule.map_exact S (T.X₁.localizedModuleMkLinearMap S)
    (T.X₂.localizedModuleMkLinearMap S) (T.X₃.localizedModuleMkLinearMap S) _ _ h

中文:
引理 localizedModuleFunctor_map_exact
  结论: [Small.{v} R] (S : 子幺半群 R)
  证明: by
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact IsLocalizedModule.map_exact S (T.X₁.localizedModuleMkLinearMap S)
    (T.X₂.localizedModuleMkLinearMap S) (T.X₃.localizedModuleMkLinearMap S) _ _ h

Depends on / 依赖: CategoryTheory, CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact, IsLocalizedModule, IsLocalizedModule.map_exact, ShortComplex, ShortExact, localizedModuleMkLinearMap, map_exact, moduleCat_exact_iff_function_exact
-/
lemma localizedModuleFunctor_map_exact [Small.{v} R] (S : Submonoid R)
    (T : ShortComplex (ModuleCat.{v} R)) (h : T.Exact) :
    (T.map (ModuleCat.localizedModuleFunctor S)).Exact := by
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact IsLocalizedModule.map_exact S (T.X₁.localizedModuleMkLinearMap S)
    (T.X₂.localizedModuleMkLinearMap S) (T.X₃.localizedModuleMkLinearMap S) _ _ h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{v}
  signature: R] (S
  body: by
  have := ((Functor.exact_tfae _).out 1 3).mp (ModuleCat.localizedModuleFunctor_map_exact S)
  exact this.1

中文:
实例 [Small.{v}
  签名: R] (S
  定义体: by
  have := ((Functor.exact_tfae _).out 1 3).mp (ModuleCat.localizedModuleFunctor_map_exact S)
  exact this.1

Depends on / 依赖: Functor, Functor.exact_tfae, ModuleCat, ModuleCat.localizedModuleFunctor_map_exact, exact_tfae, localizedModuleFunctor_map_exact
-/
instance [Small.{v} R] (S : Submonoid R) :
    Limits.PreservesFiniteLimits (ModuleCat.localizedModuleFunctor.{v} S) := by
  have := ((Functor.exact_tfae _).out 1 3).mp (ModuleCat.localizedModuleFunctor_map_exact S)
  exact this.1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{v}
  signature: R] (S
  body: by
  have := ((Functor.exact_tfae _).out 1 3).mp (ModuleCat.localizedModuleFunctor_map_exact S)
  exact this.2

中文:
实例 [Small.{v}
  签名: R] (S
  定义体: by
  have := ((Functor.exact_tfae _).out 1 3).mp (ModuleCat.localizedModuleFunctor_map_exact S)
  exact this.2

Depends on / 依赖: Functor, Functor.exact_tfae, ModuleCat, ModuleCat.localizedModuleFunctor_map_exact, exact_tfae, localizedModuleFunctor_map_exact
-/
instance [Small.{v} R] (S : Submonoid R) :
    Limits.PreservesFiniteColimits (ModuleCat.localizedModuleFunctor.{v} S) := by
  have := ((Functor.exact_tfae _).out 1 3).mp (ModuleCat.localizedModuleFunctor_map_exact S)
  exact this.2

/--
lemma `isIso_of_isLocalizedModule_comp` / 引理 `isIso_of_isLocalizedModule_comp`

English:
lemma isIso_of_isLocalizedModule_comp
  statement: {S : Submonoid R} {M₁ M₂ M₃ : ModuleCat R} {f₁ : M₁ ⟶ M₂}
  proof: by
  have : Function.Bijective f₂.hom := by
    rw [← IsLocalizedModule.linearEquiv_of_isLocalizedModule_comp S f₁.hom f₂.hom]
    exact (IsLocalizedModule.linearEquiv ..).bijective
  simpa [ConcreteCategory.isIso_iff_bijective]

中文:
引理 isIso_of_isLocalizedModule_comp
  结论: {S : 子幺半群 R} {M₁ M₂ M₃ : 模范畴 R} {f₁ : M₁ ⟶ M₂}
  证明: by
  have : Function.Bijective f₂.hom := by
    rw [← IsLocalizedModule.linearEquiv_of_isLocalizedModule_comp S f₁.hom f₂.hom]
    exact (IsLocalizedModule.linearEquiv ..).bijective
  simpa [ConcreteCategory.isIso_iff_bijective]

Depends on / 依赖: Bijective, ConcreteCategory, ConcreteCategory.isIso_iff_bijective, Function, Function.Bijective, IsLocalizedModule, IsLocalizedModule.linearEquiv, IsLocalizedModule.linearEquiv_of_isLocalizedModule_comp, bijective, isIso_iff_bijective, linearEquiv, linearEquiv_of_isLocalizedModule_comp
-/
lemma isIso_of_isLocalizedModule_comp {S : Submonoid R} {M₁ M₂ M₃ : ModuleCat R} {f₁ : M₁ ⟶ M₂}
    {f₂ : M₂ ⟶ M₃} (h₁ : IsLocalizedModule S f₁.hom) (h₂ : IsLocalizedModule S (f₁ ≫ f₂).hom) :
    IsIso f₂ := by
  have : Function.Bijective f₂.hom := by
    rw [← IsLocalizedModule.linearEquiv_of_isLocalizedModule_comp S f₁.hom f₂.hom]
    exact (IsLocalizedModule.linearEquiv ..).bijective
  simpa [ConcreteCategory.isIso_iff_bijective]

end ModuleCat
