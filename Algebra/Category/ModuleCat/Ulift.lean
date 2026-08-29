/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

/-!

# Ulift functor for ModuleCat

In this file, we define the obvious functor `ModuleCat.{v} R ⥤ ModuleCat.{max v v'} R` and prove
it is exact, fully faithful and preserves projective and injective objects.

-/

@[expose] public section

universe v' v u

variable (R : Type u)

open CategoryTheory

namespace ModuleCat

section Ring

variable [Ring R]

/-- Universe lift functor for `R`-module. -/
@[simps obj map, pp_with_univ]
/--
Definition of `uliftFunctor` / `uliftFunctor` 的定义

English:
definition uliftFunctor
  signature: : ModuleCat.{v} R ⥤ ModuleCat.{max v v'} R where
  body: ModuleCat.of R (ULift.{v', v} X)
map f := ModuleCat.ofHom
    ULift.moduleEquiv.symm.toLinearMap.comp (f.hom.comp ULift.moduleEquiv.toLinearMap)

中文:
定义 uliftFunctor
  签名: : ModuleCat.{v} R ⥤ ModuleCat.{max v v'} R where
  定义体: ModuleCat.of R (ULift.{v', v} X)
map f := ModuleCat.ofHom
    ULift.moduleEquiv.symm.toLinearMap.comp (f.hom.comp ULift.moduleEquiv.toLinearMap)

Depends on / 依赖: ModuleCat, ModuleCat.of
-/
def uliftFunctor : ModuleCat.{v} R ⥤ ModuleCat.{max v v'} R where
  obj X := ModuleCat.of R (ULift.{v', v} X)
map f := ModuleCat.ofHom
    ULift.moduleEquiv.symm.toLinearMap.comp (f.hom.comp ULift.moduleEquiv.toLinearMap)

/--
Definition of `fullyFaithfulUliftFunctor` / `fullyFaithfulUliftFunctor` 的定义

English:
definition fullyFaithfulUliftFunctor
  signature: : (uliftFunctor R).FullyFaithful where
  body: ModuleCat.ofHom (ULift.moduleEquiv.toLinearMap.comp
    (f.hom.comp ULift.moduleEquiv.symm.toLinearMap))

#adaptation_note

中文:
定义 fullyFaithfulUliftFunctor
  签名: : (uliftFunctor R).FullyFaithful where
  定义体: ModuleCat.ofHom (ULift.moduleEquiv.toLinearMap.comp
    (f.hom.comp ULift.moduleEquiv.symm.toLinearMap))

#adaptation_note

Depends on / 依赖: ModuleCat, ModuleCat.ofHom, ULift.moduleEquiv.toLinearMap.comp, moduleEquiv, toLinearMap
-/
def fullyFaithfulUliftFunctor : (uliftFunctor R).FullyFaithful where
  preimage f := ModuleCat.ofHom (ULift.moduleEquiv.toLinearMap.comp
    (f.hom.comp ULift.moduleEquiv.symm.toLinearMap))

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The `ULift` functor on `ModuleCat` is compatible with the one defined on categories of types. -/
@[simps! +dsimpLhs]
/--
Definition of `uliftFunctorForgetIso` / `uliftFunctorForgetIso` 的定义

English:
definition uliftFunctorForgetIso
  signature: :
  body: .refl _

中文:
定义 uliftFunctorForgetIso
  签名: :
  定义体: .refl _
-/
def uliftFunctorForgetIso :
    ModuleCat.uliftFunctor.{v'} R ⋙ forget _ ≅
    forget _ ⋙ CategoryTheory.uliftFunctor.{v'} :=
  .refl _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (uliftFunctor.{v', v} R).Full
  body: (fullyFaithfulUliftFunctor R).full

中文:
实例 :
  签名: (uliftFunctor.{v', v} R).Full
  定义体: (fullyFaithfulUliftFunctor R).full

Depends on / 依赖: fullyFaithfulUliftFunctor
-/
instance : (uliftFunctor.{v', v} R).Full := (fullyFaithfulUliftFunctor R).full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (uliftFunctor.{v', v} R).Faithful
  body: (fullyFaithfulUliftFunctor R).faithful

中文:
实例 :
  签名: (uliftFunctor.{v', v} R).Faithful
  定义体: (fullyFaithfulUliftFunctor R).faithful

Depends on / 依赖: faithful, fullyFaithfulUliftFunctor
-/
instance : (uliftFunctor.{v', v} R).Faithful := (fullyFaithfulUliftFunctor R).faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (uliftFunctor R).Additive

中文:
实例 :
  签名: (uliftFunctor R).Additive
-/
instance : (uliftFunctor R).Additive where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Limits.PreservesLimitsOfSize.{v, v} (uliftFunctor.{v', v} R)
  body: let : Limits.PreservesLimitsOfSize.{v, v} (uliftFunctor.{v', v} R ⋙ forget _) := by
    change Limits.PreservesLimitsOfSize.{v, v} (forget (ModuleCat R) ⋙
      CategoryTheory.uliftFunctor.{v'})
    infer_instance
  Limits.preservesLimits_of_reflects_of_preserves (uliftFunctor.{v', v} R) (forget _)

中文:
实例 :
  签名: Limits.PreservesLimitsOfSize.{v, v} (uliftFunctor.{v', v} R)
  定义体: let : Limits.PreservesLimitsOfSize.{v, v} (uliftFunctor.{v', v} R ⋙ forget _) := by
    change Limits.PreservesLimitsOfSize.{v, v} (forget (ModuleCat R) ⋙
      CategoryTheory.uliftFunctor.{v'})
    infer_instance
  Limits.preservesLimits_of_reflects_of_preserves (uliftFunctor.{v', v} R) (forget _)

Depends on / 依赖: CategoryTheory, CategoryTheory.uliftFunctor, Limits, Limits.PreservesLimitsOfSize, Limits.preservesLimits_of_reflects_of_preserves, ModuleCat, PreservesLimitsOfSize, forget, infer_instance, preservesLimits_of_reflects_of_preserves, uliftFunctor
-/
instance : Limits.PreservesLimitsOfSize.{v, v} (uliftFunctor.{v', v} R) :=
  let : Limits.PreservesLimitsOfSize.{v, v} (uliftFunctor.{v', v} R ⋙ forget _) := by
    change Limits.PreservesLimitsOfSize.{v, v} (forget (ModuleCat R) ⋙
      CategoryTheory.uliftFunctor.{v'})
    infer_instance
  Limits.preservesLimits_of_reflects_of_preserves (uliftFunctor.{v', v} R) (forget _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Limits.PreservesFiniteLimits (uliftFunctor.{v', v} R)
  body: Limits.PreservesLimitsOfSize.preservesFiniteLimits _

中文:
实例 :
  签名: Limits.PreservesFiniteLimits (uliftFunctor.{v', v} R)
  定义体: Limits.PreservesLimitsOfSize.preservesFiniteLimits _

Depends on / 依赖: Limits, Limits.PreservesLimitsOfSize.preservesFiniteLimits, PreservesLimitsOfSize, preservesFiniteLimits
-/
instance : Limits.PreservesFiniteLimits (uliftFunctor.{v', v} R) :=
  Limits.PreservesLimitsOfSize.preservesFiniteLimits _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `uliftFunctor_map_exact` / 引理 `uliftFunctor_map_exact`

English:
lemma uliftFunctor_map_exact
  given: (S : ShortComplex (ModuleCat.{v} R)) (h : S.Exact)
  proof: by
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  dsimp [uliftFunctor]
  intro x
  simp only [Function.comp_apply, Set.mem_range, LinearEquiv.symm_apply_eq, map_zero]
  rw [(CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp h]
  cat_d

中文:
引理 uliftFunctor_map_exact
  条件: (S : ShortComplex (ModuleCat.{v} R)) (h : S.Exact)
  证明: by
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  dsimp [uliftFunctor]
  intro x
  simp only [Function.comp_apply, Set.mem_range, LinearEquiv.symm_apply_eq, map_zero]
  rw [(CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp h]
  cat_d

Depends on / 依赖: CategoryTheory, CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact, Function, Function.comp_apply, LinearEquiv, LinearEquiv.symm_apply_eq, Set.mem_range, ShortComplex, ShortExact, cat_disch, comp_apply, map_zero, mem_range, moduleCat_exact_iff_function_exact, symm_apply_eq, uliftFunctor
-/
lemma uliftFunctor_map_exact (S : ShortComplex (ModuleCat.{v} R)) (h : S.Exact) :
    (S.map (uliftFunctor R)).Exact := by
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  dsimp [uliftFunctor]
  intro x
  simp only [Function.comp_apply, Set.mem_range, LinearEquiv.symm_apply_eq, map_zero]
  rw [(CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp h]
  cat_disch

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Limits.PreservesFiniteColimits (uliftFunctor.{v', v} R)
  body: by
  have := ((CategoryTheory.Functor.exact_tfae (uliftFunctor.{v', v} R)).out 1 3).mp
    (uliftFunctor_map_exact R)
  exact this.2

中文:
实例 :
  签名: Limits.PreservesFiniteColimits (uliftFunctor.{v', v} R)
  定义体: by
  have := ((CategoryTheory.Functor.exact_tfae (uliftFunctor.{v', v} R)).out 1 3).mp
    (uliftFunctor_map_exact R)
  exact this.2

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.exact_tfae, Functor, exact_tfae, uliftFunctor, uliftFunctor_map_exact
-/
instance : Limits.PreservesFiniteColimits (uliftFunctor.{v', v} R) := by
  have := ((CategoryTheory.Functor.exact_tfae (uliftFunctor.{v', v} R)).out 1 3).mp
    (uliftFunctor_map_exact R)
  exact this.2

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{v}
  signature: R] : (uliftFunctor.{v', v} R).PreservesProjectiveObjects where
  body: by
    have := small_lift.{u, v'} R
    dsimp
    infer_instance

中文:
实例 [Small.{v}
  签名: R] : (uliftFunctor.{v', v} R).PreservesProjectiveObjects where
  定义体: by
    have := small_lift.{u, v'} R
    dsimp
    infer_instance

Depends on / 依赖: infer_instance, small_lift
-/
instance [Small.{v} R] : (uliftFunctor.{v', v} R).PreservesProjectiveObjects where
  projective_obj {M} proj := by
    have := small_lift.{u, v'} R
    dsimp
    infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{v}
  signature: R] : (uliftFunctor.{v', v} R).PreservesInjectiveObjects where
  body: (Module.injective_iff_injective_object R _).mp
    (Module.ulift_injective_of_injective R ((Module.injective_iff_injective_object R M).mpr inj))

中文:
实例 [Small.{v}
  签名: R] : (uliftFunctor.{v', v} R).PreservesInjectiveObjects where
  定义体: (Module.injective_iff_injective_object R _).mp
    (Module.ulift_injective_of_injective R ((Module.injective_iff_injective_object R M).mpr inj))

Depends on / 依赖: Module, Module.injective_iff_injective_object, injective_iff_injective_object
-/
instance [Small.{v} R] : (uliftFunctor.{v', v} R).PreservesInjectiveObjects where
  injective_obj {M} inj := (Module.injective_iff_injective_object R _).mp
    (Module.ulift_injective_of_injective R ((Module.injective_iff_injective_object R M).mpr inj))

end Ring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommRing
  signature: R] : (uliftFunctor.{v', v} R).Linear R where

中文:
实例 [CommRing
  签名: R] : (uliftFunctor.{v', v} R).Linear R where
-/
instance [CommRing R] : (uliftFunctor.{v', v} R).Linear R where

end ModuleCat
