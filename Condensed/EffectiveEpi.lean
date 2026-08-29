/-
Copyright (c) 2025 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf, Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.RegularEpi
public import Mathlib.Condensed.Epi
public import Mathlib.Condensed.Functors
public import Mathlib.Condensed.Limits -- shake: keep (compHausToCondensed.PreservesEffectiveEpis), cf. lean#13417

/-!

# The functor from compact Hausdorff spaces to condensed sets preserves effective epimorphisms
-/

public section

open CategoryTheory CompHausLike

universe u

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: compHausToCondensed.PreservesEpimorphisms
  body: by
    rw [CondensedSet.epi_iff_locallySurjective_on_compHaus]
    intro S g
    refine ⟨pullback f g.down, pullback.snd _ _, fun y => ?_, ⟨pullback.fst _ _⟩,
ULift.ext _ _ pullback.condition _ _⟩
    rw [CompHaus.epi_iff_surjective] at hf
    obtain ⟨x, hx⟩ := hf (g.down.hom y)
    exact ⟨⟨⟨x, y⟩, 

中文:
实例 :
  签名: compHausToCondensed.PreservesEpimorphisms
  定义体: by
    rw [CondensedSet.epi_iff_locallySurjective_on_compHaus]
    intro S g
    refine ⟨pullback f g.down, pullback.snd _ _, fun y => ?_, ⟨pullback.fst _ _⟩,
ULift.ext _ _ pullback.condition _ _⟩
    rw [CompHaus.epi_iff_surjective] at hf
    obtain ⟨x, hx⟩ := hf (g.down.hom y)
    exact ⟨⟨⟨x, y⟩, 

Depends on / 依赖: CompHaus, CompHaus.epi_iff_surjective, CondensedSet, CondensedSet.epi_iff_locallySurjective_on_compHaus, ULift.ext, condition, epi_iff_locallySurjective_on_compHaus, epi_iff_surjective, g.down, g.down.hom, pullback, pullback.condition, pullback.fst, pullback.snd
-/
instance : compHausToCondensed.PreservesEpimorphisms where
  preserves f hf := by
    rw [CondensedSet.epi_iff_locallySurjective_on_compHaus]
    intro S g
    refine ⟨pullback f g.down, pullback.snd _ _, fun y => ?_, ⟨pullback.fst _ _⟩,
ULift.ext _ _ pullback.condition _ _⟩
    rw [CompHaus.epi_iff_surjective] at hf
    obtain ⟨x, hx⟩ := hf (g.down.hom y)
    exact ⟨⟨⟨x, y⟩, hx⟩, rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsRegularEpiCategory CondensedSet.{u}
  body: inferInstanceAs IsRegularEpiCategory (Sheaf _ _)

example : compHausToCondensed.PreservesEffectiveEpis := inferInstance

中文:
实例 :
  签名: IsRegularEpiCategory CondensedSet.{u}
  定义体: inferInstanceAs IsRegularEpiCategory (Sheaf _ _)

example : compHausToCondensed.PreservesEffectiveEpis := inferInstance

Depends on / 依赖: IsRegularEpiCategory
-/
instance : IsRegularEpiCategory CondensedSet.{u} :=
inferInstanceAs IsRegularEpiCategory (Sheaf _ _)

example : compHausToCondensed.PreservesEffectiveEpis := inferInstance
