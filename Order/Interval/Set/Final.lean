/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Final functors between intervals

-/

public section

universe u

/--
Instance `Set.Ici.subtype_functor_final` / 实例 `Set.Ici.subtype_functor_final`

English:
instance Set.Ici.subtype_functor_final
  signature: {J : Type u} [LinearOrder J] (j : J)
  body: by
  rw [Monotone.final_functor_iff]
  intro k
  exact ⟨⟨max j k, le_max_left _ _⟩, le_max_right _ _⟩

中文:
实例 Set.Ici.subtype_functor_final
  签名: {J : 类型u} [LinearOrder J] (j : J)
  定义体: by
  rw [Monotone.final_functor_iff]
  intro k
  exact ⟨⟨max j k, le_max_left _ _⟩, le_max_right _ _⟩

Depends on / 依赖: Monotone, Monotone.final_functor_iff, final_functor_iff, le_max_left, le_max_right
-/
instance Set.Ici.subtype_functor_final {J : Type u} [LinearOrder J] (j : J) :
    (Subtype.mono_coe (· in Set.Ici j)).functor.Final := by
  rw [Monotone.final_functor_iff]
  intro k
  exact ⟨⟨max j k, le_max_left _ _⟩, le_max_right _ _⟩
