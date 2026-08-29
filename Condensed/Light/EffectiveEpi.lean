/-
Copyright (c) 2025 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf, Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.RegularEpi
public import Mathlib.Condensed.Light.Epi
public import Mathlib.Condensed.Light.Functors

/-!

# The functor from light profinite sets to light condensed sets preserves effective epimorphisms
-/

public section

open CategoryTheory CompHausLike

universe u

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: lightProfiniteToLightCondSet.PreservesEpimorphisms
  body: by
    rw [LightCondSet.epi_iff_locallySurjective_on_lightProfinite]
    intro S g
    refine ⟨pullback f g, pullback.snd _ _, fun y => ?_, pullback.fst _ _, pullback.condition _ _⟩
    rw [LightProfinite.epi_iff_surjective] at hf
    obtain ⟨x, hx⟩ := hf (g.hom y)
    exact ⟨⟨⟨x, y⟩, hx⟩, rfl⟩

中文:
实例 :
  签名: lightProfiniteToLightCondSet.保持Epimorphisms
  定义体: by
    rw [LightCondSet.epi_iff_locallySurjective_on_lightProfinite]
    intro S g
    refine ⟨pullback f g, pullback.snd _ _, fun y => ?_, pullback.fst _ _, pullback.condition _ _⟩
    rw [LightProfinite.epi_iff_surjective] at hf
    obtain ⟨x, hx⟩ := hf (g.hom y)
    exact ⟨⟨⟨x, y⟩, hx⟩, rfl⟩

Depends on / 依赖: LightCondSet, LightCondSet.epi_iff_locallySurjective_on_lightProfinite, LightProfinite, LightProfinite.epi_iff_surjective, condition, epi_iff_locallySurjective_on_lightProfinite, epi_iff_surjective, g.hom, pullback, pullback.condition, pullback.fst, pullback.snd
-/
instance : lightProfiniteToLightCondSet.PreservesEpimorphisms where
  preserves f hf := by
    rw [LightCondSet.epi_iff_locallySurjective_on_lightProfinite]
    intro S g
    refine ⟨pullback f g, pullback.snd _ _, fun y => ?_, pullback.fst _ _, pullback.condition _ _⟩
    rw [LightProfinite.epi_iff_surjective] at hf
    obtain ⟨x, hx⟩ := hf (g.hom y)
    exact ⟨⟨⟨x, y⟩, hx⟩, rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsRegularEpiCategory LightCondSet.{u}
  body: inferInstanceAs IsRegularEpiCategory (Sheaf _ _)

example : lightProfiniteToLightCondSet.PreservesEffectiveEpis := inferInstance

中文:
实例 :
  签名: 是正则满态射范畴 LightCondSet.{u}
  定义体: inferInstanceAs IsRegularEpiCategory (Sheaf _ _)

example : lightProfiniteToLightCondSet.PreservesEffectiveEpis := inferInstance

Depends on / 依赖: IsRegularEpiCategory
-/
instance : IsRegularEpiCategory LightCondSet.{u} :=
inferInstanceAs IsRegularEpiCategory (Sheaf _ _)

example : lightProfiniteToLightCondSet.PreservesEffectiveEpis := inferInstance
