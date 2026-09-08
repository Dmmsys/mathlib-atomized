/-
Copyright (c) 2025 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf, Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.RegularEpi
public import Mathlib.Condensed.Epi
public import Mathlib.Condensed.Functors
public import Mathlib.Condensed.Limits  -- shake: keep (compHausToCondensed.PreservesEffectiveEpis), cf. lean#13417

/-!

# The functor from compact Hausdorff spaces to condensed sets preserves effective epimorphisms
-/

public section

open CategoryTheory CompHausLike

universe u

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : compHausToCondensed.PreservesEpimorphisms where
  preserves f hf := by
    rw [CondensedSet.epi_iff_locallySurjective_on_compHaus]
    intro S g
    refine ⟨pullback f g.down, pullback.snd _ _, fun y ↦ ?_, ⟨pullback.fst _ _⟩,
      ULift.ext _ _ <| pullback.condition _ _⟩
    rw [CompHaus.epi_iff_surjective] at hf
    obtain ⟨x, hx⟩ := hf (g.down.hom y)
    exact ⟨⟨⟨x, y⟩, hx⟩, rfl⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsRegularEpiCategory CondensedSet.{u} :=
  inferInstanceAs <| IsRegularEpiCategory (Sheaf _ _)
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : compHausToCondensed.PreservesEffectiveEpis := inferInstance
