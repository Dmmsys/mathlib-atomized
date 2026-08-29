/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Generator.Basic

/-!
# Generator of Type

In this file, we show that `PUnit` is a separator of the category `Type u`.

-/

public section

universe u

namespace CategoryTheory

/--
lemma `Types.isSeparator_punit` / 引理 `Types.isSeparator_punit`

English:
lemma Types.isSeparator_punit
  statement: IsSeparator (PUnit.{u + 1})
  proof: by
  intro X Y f g h
  ext x
  exact ConcreteCategory.congr_hom (h PUnit (by simp) (↾fun _ => x))
    .unit

中文:
引理 Types.isSeparator_punit
  结论: IsSeparator (命题单元.{u + 1})
  证明: by
  intro X Y f g h
  ext x
  exact ConcreteCategory.congr_hom (h PUnit (by simp) (↾fun _ => x))
    .unit

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_hom
-/
lemma Types.isSeparator_punit : IsSeparator (PUnit.{u + 1}) := by
  intro X Y f g h
  ext x
  exact ConcreteCategory.congr_hom (h PUnit (by simp) (↾fun _ => x))
    .unit

end CategoryTheory
