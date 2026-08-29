/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Stability properties of epimorphisms in `Type`

In this file, we show that in the category `Type u`, epimorphisms
are stable under base change.

-/

public section

universe u

namespace CategoryTheory.Types

open MorphismProperty Limits

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (epimorphisms (Type u)).IsStableUnderBaseChange
  body: by
    simp only [epimorphisms.iff, epi_iff_surjective] at hr ⊢
    intro x
    obtain ⟨y, hy⟩ := hr (b x)
    obtain ⟨z, _, hz⟩ := Types.exists_of_isPullback sq _ _ hy
    exact ⟨z, hz⟩

中文:
实例 :
  签名: (epimorphisms (类型u)).IsStableUnderBaseChange
  定义体: by
    simp only [epimorphisms.iff, epi_iff_surjective] at hr ⊢
    intro x
    obtain ⟨y, hy⟩ := hr (b x)
    obtain ⟨z, _, hz⟩ := Types.exists_of_isPullback sq _ _ hy
    exact ⟨z, hz⟩

Depends on / 依赖: Types.exists_of_isPullback, epi_iff_surjective, epimorphisms, epimorphisms.iff, exists_of_isPullback
-/
instance : (epimorphisms (Type u)).IsStableUnderBaseChange where
  of_isPullback {_ _ _ _} b r t l sq hr := by
    simp only [epimorphisms.iff, epi_iff_surjective] at hr ⊢
    intro x
    obtain ⟨y, hy⟩ := hr (b x)
    obtain ⟨z, _, hz⟩ := Types.exists_of_isPullback sq _ _ hy
    exact ⟨z, hz⟩

end CategoryTheory.Types
