/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Generator.Abelian

/-!
# Grothendieck categories have a coseparator
-/

public section

universe w v u

namespace CategoryTheory.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasCoseparator C
  body: by
  suffices HasCoseparator (ShrinkHoms C) from
    HasCoseparator.of_equivalence (ShrinkHoms.equivalence.{w} C).symm
  obtain ⟨G, -, hG⟩ := Abelian.has_injective_coseparator (separator (ShrinkHoms C))
    (isSeparator_separator _)
  exact ⟨G, hG⟩

中文:
实例 :
  签名: HasCoseparator C
  定义体: by
  suffices HasCoseparator (ShrinkHoms C) from
    HasCoseparator.of_equivalence (ShrinkHoms.equivalence.{w} C).symm
  obtain ⟨G, -, hG⟩ := Abelian.has_injective_coseparator (separator (ShrinkHoms C))
    (isSeparator_separator _)
  exact ⟨G, hG⟩

Depends on / 依赖: Abelian, Abelian.has_injective_coseparator, HasCoseparator, HasCoseparator.of_equivalence, ShrinkHoms, ShrinkHoms.equivalence, equivalence, has_injective_coseparator, isSeparator_separator, of_equivalence, separator
-/
instance : HasCoseparator C := by
  suffices HasCoseparator (ShrinkHoms C) from
    HasCoseparator.of_equivalence (ShrinkHoms.equivalence.{w} C).symm
  obtain ⟨G, -, hG⟩ := Abelian.has_injective_coseparator (separator (ShrinkHoms C))
    (isSeparator_separator _)
  exact ⟨G, hG⟩

end CategoryTheory.IsGrothendieckAbelian
