/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Limits.Indization.Category
public import Mathlib.CategoryTheory.Preadditive.Indization

/-!
# Separating set in the category of ind-objects

We construct a separating set in the category of ind-objects and conclude that if `C` is small
and additive, then `Ind C` has a separator.

-/

public section

universe v u

namespace CategoryTheory

open Limits

section

variable {C : Type u} [Category.{v} C]

/--
theorem `Ind.isSeparating_range_yoneda` / 定理 `Ind.isSeparating_range_yoneda`

English:
theorem Ind.isSeparating_range_yoneda
  proof: by
  refine fun X Y f g h => (cancel_epi (Ind.colimitPresentationCompYoneda X).hom).1 ?_
  exact colimit.hom_ext (fun i => by simp [← Category.assoc, h])

中文:
定理 Ind.isSeparating_range_yoneda
  证明: by
  refine fun X Y f g h => (cancel_epi (Ind.colimitPresentationCompYoneda X).hom).1 ?_
  exact colimit.hom_ext (fun i => by simp [← Category.assoc, h])

Depends on / 依赖: Category, Category.assoc, Ind.colimitPresentationCompYoneda, cancel_epi, colimit, colimit.hom_ext, colimitPresentationCompYoneda, hom_ext, leftRetraction, rightRetraction
-/
theorem Ind.isSeparating_range_yoneda :
    ObjectProperty.IsSeparating (.ofObj (Ind.yoneda : C ⥤ _).obj) := by
  refine fun X Y f g h => (cancel_epi (Ind.colimitPresentationCompYoneda X).hom).1 ?_
  exact colimit.hom_ext (fun i => by simp [← Category.assoc, h])

end

section

variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteColimits C]

/--
theorem `Ind.isSeparator_range_yoneda` / 定理 `Ind.isSeparator_range_yoneda`

English:
theorem Ind.isSeparator_range_yoneda
  statement: IsSeparator (∐ (Ind.yoneda : C ⥤ _).obj)
  proof: Ind.isSeparating_range_yoneda.isSeparator_coproduct

中文:
定理 Ind.isSeparator_range_yoneda
  结论: IsSeparator (∐ (Ind.yoneda : C ⥤ _).obj)
  证明: Ind.isSeparating_range_yoneda.isSeparator_coproduct

Depends on / 依赖: Ind.isSeparating_range_yoneda.isSeparator_coproduct, isSeparating_range_yoneda, isSeparator_coproduct
-/
theorem Ind.isSeparator_range_yoneda : IsSeparator (∐ (Ind.yoneda : C ⥤ _).obj) :=
  Ind.isSeparating_range_yoneda.isSeparator_coproduct

end

end CategoryTheory
