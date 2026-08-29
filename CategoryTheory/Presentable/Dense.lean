/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Functor.KanExtension.Dense
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.Presentable.Finite

/-!
# `κ`-presentable objects form a dense subcategory

In a `κ`-accessible category `C`, the inclusion of the full subcategory
of `κ`-presentable objects is a dense functor. This expresses canonically
any object `X : C` as a colimit of `κ`-presentable objects, and we show
that this is a `κ`-filtered colimit.

-/

public section

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C] {κ : Cardinal.{w}} [Fact κ.IsRegular]

variable (C κ) in
/--
lemma `isCardinalFilteredGenerator_isCardinalPresentable` / 引理 `isCardinalFilteredGenerator_isCardinalPresentable`

English:
lemma isCardinalFilteredGenerator_isCardinalPresentable
  proof: by
  obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_generator C κ
  refine hP.of_le_isoClosure ?_ le_rfl
  rw [ObjectProperty.isoClosure_eq_self]
  exact hP.le_isCardinalPresentable

中文:
引理 isCardinalFilteredGenerator_isCardinalPresentable
  证明: by
  obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_generator C κ
  refine hP.of_le_isoClosure ?_ le_rfl
  rw [ObjectProperty.isoClosure_eq_self]
  exact hP.le_isCardinalPresentable

Depends on / 依赖: HasCardinalFilteredGenerator, HasCardinalFilteredGenerator.exists_generator, ObjectProperty, ObjectProperty.isoClosure_eq_self, exists_generator, hP.le_isCardinalPresentable, hP.of_le_isoClosure, isoClosure_eq_self, le_isCardinalPresentable, le_rfl, of_le_isoClosure
-/
lemma isCardinalFilteredGenerator_isCardinalPresentable
    [IsCardinalAccessibleCategory C κ] :
    (isCardinalPresentable C κ).IsCardinalFilteredGenerator κ := by
  obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_generator C κ
  refine hP.of_le_isoClosure ?_ le_rfl
  rw [ObjectProperty.isoClosure_eq_self]
  exact hP.le_isCardinalPresentable

namespace IsCardinalAccessibleCategory

/--
Instance `final_toCostructuredArrow` / 实例 `final_toCostructuredArrow`

English:
instance final_toCostructuredArrow
  body: by
  have := isFiltered_of_isCardinalFiltered J κ
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨fun f => ?_, fun {f j} g₁ g₂ => ?_⟩
  · obtain ⟨j, g, hg⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit f.hom
    exact ⟨j, ⟨CostructuredArrow.homMk (ObjectProperty.homMk g)⟩⟩
  · obta

中文:
实例 final_toCostructuredArrow
  定义体: by
  have := isFiltered_of_isCardinalFiltered J κ
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨fun f => ?_, fun {f j} g₁ g₂ => ?_⟩
  · obtain ⟨j, g, hg⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit f.hom
    exact ⟨j, ⟨CostructuredArrow.homMk (ObjectProperty.homMk g)⟩⟩
  · obta

Depends on / 依赖: CostructuredArrow, CostructuredArrow.homMk, CostructuredArrow.w, Functor, Functor.final_iff_of_isFiltered, IsCardinalPresentable, IsCardinalPresentable.exists_eq_of_isColimit, IsCardinalPresentable.exists_hom_of_isColimit, ObjectProperty, ObjectProperty.homMk, cat_disch, exists_eq_of_isColimit, exists_hom_of_isColimit, f.hom, final_iff_of_isFiltered, isColimit, isFiltered_of_isCardinalFiltered, left.hom, p.isColimit
-/
instance final_toCostructuredArrow
    {J : Type u'} [Category.{v'} J] [EssentiallySmall.{w} J]
    [IsCardinalFiltered J κ] {X : C}
    (p : (isCardinalPresentable C κ).ColimitOfShape J X) :
    p.toCostructuredArrow.Final := by
  have := isFiltered_of_isCardinalFiltered J κ
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨fun f => ?_, fun {f j} g₁ g₂ => ?_⟩
  · obtain ⟨j, g, hg⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit f.hom
    exact ⟨j, ⟨CostructuredArrow.homMk (ObjectProperty.homMk g)⟩⟩
  · obtain ⟨k, a, h⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ p.isColimit
      g₁.left.hom g₂.left.hom ((CostructuredArrow.w g₁).trans (CostructuredArrow.w g₂).symm)
    exact ⟨k, a, by cat_disch⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCardinalAccessibleCategory
  signature: C κ] :
  body: by
    obtain ⟨J, _, _, ⟨p⟩⟩ :=
      (isCardinalFilteredGenerator_isCardinalPresentable C κ).exists_colimitsOfShape X
    exact ⟨(Functor.Final.isColimitWhiskerEquiv (F := p.toCostructuredArrow) _).1
      (IsColimit.ofIsoColimit p.isColimit (Cocone.ext (Iso.refl _)))⟩

中文:
实例 [IsCardinalAccessibleCategory
  签名: C κ] :
  定义体: by
    obtain ⟨J, _, _, ⟨p⟩⟩ :=
      (isCardinalFilteredGenerator_isCardinalPresentable C κ).exists_colimitsOfShape X
    exact ⟨(Functor.Final.isColimitWhiskerEquiv (F := p.toCostructuredArrow) _).1
      (IsColimit.ofIsoColimit p.isColimit (Cocone.ext (Iso.refl _)))⟩

Depends on / 依赖: Cocone, Cocone.ext, Functor, Functor.Final.isColimitWhiskerEquiv, IsColimit, IsColimit.ofIsoColimit, Iso.refl, exists_colimitsOfShape, isCardinalFilteredGenerator_isCardinalPresentable, isColimit, isColimitWhiskerEquiv, ofIsoColimit, p.isColimit, p.toCostructuredArrow, toCostructuredArrow
-/
instance [IsCardinalAccessibleCategory C κ] :
    (isCardinalPresentable C κ).ι.IsDense where
  isDenseAt X := by
    obtain ⟨J, _, _, ⟨p⟩⟩ :=
      (isCardinalFilteredGenerator_isCardinalPresentable C κ).exists_colimitsOfShape X
    exact ⟨(Functor.Final.isColimitWhiskerEquiv (F := p.toCostructuredArrow) _).1
      (IsColimit.ofIsoColimit p.isColimit (Cocone.ext (Iso.refl _)))⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCardinalAccessibleCategory
  signature: C κ] (X
  body: by
  obtain ⟨J, _, _, ⟨p⟩⟩ :=
    (isCardinalFilteredGenerator_isCardinalPresentable C κ).exists_colimitsOfShape X
  exact IsCardinalFiltered.of_final p.toCostructuredArrow κ

中文:
实例 [IsCardinalAccessibleCategory
  签名: C κ] (X
  定义体: by
  obtain ⟨J, _, _, ⟨p⟩⟩ :=
    (isCardinalFilteredGenerator_isCardinalPresentable C κ).exists_colimitsOfShape X
  exact IsCardinalFiltered.of_final p.toCostructuredArrow κ

Depends on / 依赖: IsCardinalFiltered, IsCardinalFiltered.of_final, exists_colimitsOfShape, isCardinalFilteredGenerator_isCardinalPresentable, of_final, p.toCostructuredArrow, toCostructuredArrow
-/
instance [IsCardinalAccessibleCategory C κ] (X : C) :
    IsCardinalFiltered (CostructuredArrow (isCardinalPresentable C κ).ι X) κ := by
  obtain ⟨J, _, _, ⟨p⟩⟩ :=
    (isCardinalFilteredGenerator_isCardinalPresentable C κ).exists_colimitsOfShape X
  exact IsCardinalFiltered.of_final p.toCostructuredArrow κ

end IsCardinalAccessibleCategory

namespace IsFinitelyAccessibleCategory

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFinitelyAccessibleCategory.{w}
  signature: C] (X
  body: by
  rw [← CategoryTheory.isCardinalFiltered_aleph0_iff.{w}]; rw [ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable]
  infer_instance

中文:
实例 [IsFinitelyAccessibleCategory.{w}
  签名: C] (X
  定义体: by
  rw [← CategoryTheory.isCardinalFiltered_aleph0_iff.{w}]; rw [ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable]
  infer_instance

Depends on / 依赖: CategoryTheory, CategoryTheory.isCardinalFiltered_aleph0_iff, ObjectProperty, ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable, infer_instance, isCardinalFiltered_aleph0_iff, isFinitelyPresentable_eq_isCardinalPresentable
-/
instance [IsFinitelyAccessibleCategory.{w} C] (X : C) :
    IsFiltered (CostructuredArrow (ObjectProperty.isFinitelyPresentable.{w} C).ι X) := by
  rw [← CategoryTheory.isCardinalFiltered_aleph0_iff.{w}]; rw [ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFinitelyAccessibleCategory.{w}
  signature: C] :
  body: by
  rw [ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable]
  infer_instance

中文:
实例 [IsFinitelyAccessibleCategory.{w}
  签名: C] :
  定义体: by
  rw [ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable]
  infer_instance

Depends on / 依赖: ObjectProperty, ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable, infer_instance, isFinitelyPresentable_eq_isCardinalPresentable
-/
instance [IsFinitelyAccessibleCategory.{w} C] :
    (ObjectProperty.isFinitelyPresentable.{w} C).ι.IsDense := by
  rw [ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFinitelyAccessibleCategory.{w}
  signature: C] :
  body: by
  rw [ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable]
  infer_instance

中文:
实例 [IsFinitelyAccessibleCategory.{w}
  签名: C] :
  定义体: by
  rw [ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable]
  infer_instance

Depends on / 依赖: ObjectProperty, ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable, infer_instance, isFinitelyPresentable_eq_isCardinalPresentable
-/
instance [IsFinitelyAccessibleCategory.{w} C] :
    ObjectProperty.EssentiallySmall.{w} (ObjectProperty.isFinitelyPresentable.{w} C) := by
  rw [ObjectProperty.isFinitelyPresentable_eq_isCardinalPresentable]
  infer_instance

end IsFinitelyAccessibleCategory

end CategoryTheory
