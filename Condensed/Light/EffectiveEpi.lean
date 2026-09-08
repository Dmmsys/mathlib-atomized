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

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : lightProfiniteToLightCondSet.PreservesEpimorphisms where
  preserves f hf := by
    rw [LightCondSet.epi_iff_locallySurjective_on_lightProfinite]
    intro S g
    refine ⟨pullback f g, pullback.snd _ _, fun y ↦ ?_, pullback.fst _ _, pullback.condition _ _⟩
    rw [LightProfinite.epi_iff_surjective] at hf
    obtain ⟨x, hx⟩ := hf (g.hom y)
    exact ⟨⟨⟨x, y⟩, hx⟩, rfl⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsRegularEpiCategory LightCondSet.{u} :=
  inferInstanceAs <| IsRegularEpiCategory (Sheaf _ _)
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : lightProfiniteToLightCondSet.PreservesEffectiveEpis := inferInstance
