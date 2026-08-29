/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Compatibility lemmas for limits and colimits in a monoidal category

For numerous simp lemmas of the form `f ≫ g = h`, we add accompanying simp lemmas of the form
`Q ◁ f ≫ Q ◁ g = Q ◁ h` and `f ▷ Q ≫ g ▷ Q = h ▷ Q`. This file and
`Mathlib.CategoryTheory.Monoidal.Limits.Shapes.Pullback` are needed to define a monoidal category
structure in `Mathlib.CategoryTheory.Monoidal.Arrow`.

## TODO
An attribute should be developed to automatically generate lemmas of this form.
-/

public section

universe v v₁ u u₁

namespace CategoryTheory.MonoidalCategory

open Limits MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace Limits

section HasColimit

variable {J : Type u₁} [Category.{v₁} J]
    {F G : J ⥤ C} [HasColimit F] [HasColimit G]

@[reassoc (attr := simp)]
/--
lemma `HasColimit.whiskerLeft_isoOfNatIso_ι_hom` / 引理 `HasColimit.whiskerLeft_isoOfNatIso_ι_hom`

English:
lemma HasColimit.whiskerLeft_isoOfNatIso_ι_hom
  given: (w : F ≅ G) (j : J) {Q : C}
  proof: by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]

中文:
引理 有余极限.whiskerLeft_isoOf自然数Iso_ι_hom
  条件: (w : F ≅ G) (j : J) {Q : C}
  证明: by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.whiskerLeft_comp, whiskerLeft_comp
-/
lemma HasColimit.whiskerLeft_isoOfNatIso_ι_hom (w : F ≅ G) (j : J) {Q : C} :
    Q ◁ colimit.ι F j ≫ Q ◁ (HasColimit.isoOfNatIso w).hom =
      Q ◁ w.hom.app j ≫ Q ◁ colimit.ι G j := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
/--
lemma `HasColimit.isoOfNatIso_ι_hom_whiskerRight` / 引理 `HasColimit.isoOfNatIso_ι_hom_whiskerRight`

English:
lemma HasColimit.isoOfNatIso_ι_hom_whiskerRight
  given: (w : F ≅ G) (j : J) {Q : C}
  proof: by
  simp [← MonoidalCategory.comp_whiskerRight]

中文:
引理 有余极限.isoOf自然数Iso_ι_hom_whiskerRight
  条件: (w : F ≅ G) (j : J) {Q : C}
  证明: by
  simp [← MonoidalCategory.comp_whiskerRight]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.comp_whiskerRight, comp_whiskerRight
-/
lemma HasColimit.isoOfNatIso_ι_hom_whiskerRight (w : F ≅ G) (j : J) {Q : C} :
    colimit.ι F j ▷ Q ≫ (HasColimit.isoOfNatIso w).hom ▷ Q =
      w.hom.app j ▷ Q ≫ colimit.ι G j ▷ Q := by
  simp [← MonoidalCategory.comp_whiskerRight]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `colimit.whiskerLeft_ι_desc` / 引理 `colimit.whiskerLeft_ι_desc`

English:
lemma colimit.whiskerLeft_ι_desc
  given: (c : Cocone F) (j : J) {Q : C}
  proof: by
  simp [← MonoidalCategory.whiskerLeft_comp]

中文:
引理 colimit.whiskerLeft_ι_desc
  条件: (c : 余锥 F) (j : J) {Q : C}
  证明: by
  simp [← MonoidalCategory.whiskerLeft_comp]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.whiskerLeft_comp, whiskerLeft_comp
-/
lemma colimit.whiskerLeft_ι_desc (c : Cocone F) (j : J) {Q : C} :
    Q ◁ colimit.ι F j ≫ Q ◁ colimit.desc F c = Q ◁ c.ι.app j := by
  simp [← MonoidalCategory.whiskerLeft_comp]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `colimit.ι_desc_whiskerRight` / 引理 `colimit.ι_desc_whiskerRight`

English:
lemma colimit.ι_desc_whiskerRight
  given: (c : Cocone F) (j : J) {Q : C}
  proof: by
  simp [← comp_whiskerRight]

中文:
引理 colimit.ι_desc_whiskerRight
  条件: (c : 余锥 F) (j : J) {Q : C}
  证明: by
  simp [← comp_whiskerRight]

Depends on / 依赖: comp_whiskerRight
-/
lemma colimit.ι_desc_whiskerRight (c : Cocone F) (j : J) {Q : C} :
    colimit.ι F j ▷ Q ≫ colimit.desc F c ▷ Q = c.ι.app j ▷ Q := by
  simp [← comp_whiskerRight]

end HasColimit

end Limits

end CategoryTheory.MonoidalCategory
