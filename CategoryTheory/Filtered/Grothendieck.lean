/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Grothendieck

/-!
# Filteredness of Grothendieck construction

We show that if `F : C ⥤ Cat` is such that `C` is filtered and `F.obj c` is filtered for all
`c : C`, then `Grothendieck F` is filtered.
-/

public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (F : C ⥤ Cat)

open IsFiltered

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFilteredOrEmpty
  signature: C] [forall c, IsFilteredOrEmpty (F.obj c)] :
  body: by
  refine ⟨?_, ?_⟩
  · rintro ⟨c, f⟩ ⟨d, g⟩
    exact ⟨⟨max c d, max ((F.map (leftToMax c d)).toFunctor.obj f)
      ((F.map (rightToMax c d)).toFunctor.obj g)⟩,
      ⟨leftToMax c d, leftToMax _ _⟩, ⟨rightToMax c d, rightToMax _ _⟩, trivial⟩
  · rintro ⟨c, f⟩ ⟨d, g⟩ ⟨u, x⟩ ⟨v, y⟩
    refine ⟨⟨coe

中文:
实例 [是FilteredOrEmpty
  签名: C] [对任意 c, 是FilteredOrEmpty (F.obj c)] :
  定义体: by
  refine ⟨?_, ?_⟩
  · rintro ⟨c, f⟩ ⟨d, g⟩
    exact ⟨⟨max c d, max ((F.map (leftToMax c d)).toFunctor.obj f)
      ((F.map (rightToMax c d)).toFunctor.obj g)⟩,
      ⟨leftToMax c d, leftToMax _ _⟩, ⟨rightToMax c d, rightToMax _ _⟩, trivial⟩
  · rintro ⟨c, f⟩ ⟨d, g⟩ ⟨u, x⟩ ⟨v, y⟩
    refine ⟨⟨coe

Depends on / 依赖: Cat.Hom, Cat.Hom.comp_obj, F.map, F.map_comp, coeqHom, coeq_condition, comp_obj, conv_rhs, eqToHom, leftToMax, map_comp, rightToMax, toFunctor, toFunctor.map, toFunctor.obj
-/
instance [IsFilteredOrEmpty C] [forall c, IsFilteredOrEmpty (F.obj c)] :
    IsFilteredOrEmpty (Grothendieck F) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨c, f⟩ ⟨d, g⟩
    exact ⟨⟨max c d, max ((F.map (leftToMax c d)).toFunctor.obj f)
      ((F.map (rightToMax c d)).toFunctor.obj g)⟩,
      ⟨leftToMax c d, leftToMax _ _⟩, ⟨rightToMax c d, rightToMax _ _⟩, trivial⟩
  · rintro ⟨c, f⟩ ⟨d, g⟩ ⟨u, x⟩ ⟨v, y⟩
    refine ⟨⟨coeq u v, coeq (eqToHom ?_ ≫
        (F.map (coeqHom u v)).toFunctor.map x) ((F.map (coeqHom u v)).toFunctor.map y)⟩,
          ⟨coeqHom u v, coeqHom _ _⟩, ?_⟩
    · conv_rhs => rw [← Cat.Hom.comp_obj, ← F.map_comp, coeq_condition, F.map_comp,
        Cat.Hom.comp_obj]
    · set_option backward.isDefEq.respectTransparency.types false in
      apply Grothendieck.ext _ _ (coeq_condition u v)
      refine Eq.trans ?_ (eqToHom _ ≫= coeq_condition _ _)
      simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFiltered
  signature: C] [forall c, IsFiltered (F.obj c)] : IsFiltered (Grothendieck F)
  body: by
  have : Nonempty (Grothendieck F) := by
    obtain ⟨c⟩ : Nonempty C := IsFiltered.nonempty
    obtain ⟨f⟩ : Nonempty (F.obj c) := IsFiltered.nonempty
    exact ⟨⟨c, f⟩⟩
  apply IsFiltered.mk

中文:
实例 [是Filtered
  签名: C] [对任意 c, 是Filtered (F.obj c)] : 是Filtered (Grothendieck F)
  定义体: by
  have : Nonempty (Grothendieck F) := by
    obtain ⟨c⟩ : Nonempty C := IsFiltered.nonempty
    obtain ⟨f⟩ : Nonempty (F.obj c) := IsFiltered.nonempty
    exact ⟨⟨c, f⟩⟩
  apply IsFiltered.mk

Depends on / 依赖: F.obj, Grothendieck, IsFiltered, IsFiltered.mk, IsFiltered.nonempty, Nonempty, nonempty
-/
instance [IsFiltered C] [forall c, IsFiltered (F.obj c)] : IsFiltered (Grothendieck F) := by
  have : Nonempty (Grothendieck F) := by
    obtain ⟨c⟩ : Nonempty C := IsFiltered.nonempty
    obtain ⟨f⟩ : Nonempty (F.obj c) := IsFiltered.nonempty
    exact ⟨⟨c, f⟩⟩
  apply IsFiltered.mk

end CategoryTheory
