/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.Monad.Limits

/-!
# Presentable objects and adjunctions

If `adj : F ⊣ G` and `G` is `κ`-accessible for a regular cardinal `κ`,
then `F` preserves `κ`-presentable objects.

Moreover, if `G : D ⥤ C` is fully faithful, then `D` is locally `κ`-presentable
(resp `κ`-accessible) if `C` is.

In particular, if `e : C ≌ D` is an equivalence of categories and
`C` is locally presentable (resp. accessible), then so is `D`.

-/

public section

universe w v v' u u'

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]

namespace Adjunction

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (κ : Cardinal.{w}) [Fact κ.IsRegular]

include adj

/--
lemma `isCardinalPresentable_leftAdjoint_obj` / 引理 `isCardinalPresentable_leftAdjoint_obj`

English:
lemma isCardinalPresentable_leftAdjoint_obj
  statement: (X : C) [IsCardinalPresentable X κ]
  proof: by
  rw [isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj.{v}]
  exact Functor.isCardinalAccessible_of_natIso
    (show G ⋙ _ ≅ _ from (Adjunction.compUliftCoyonedaIso.{0} adj).symm.app (op X)) κ

中文:
引理 isCardinalPresentable_leftAdjoint_obj
  结论: (X : C) [IsCardinalPresentable X κ]
  证明: by
  rw [isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj.{v}]
  exact Functor.isCardinalAccessible_of_natIso
    (show G ⋙ _ ≅ _ from (Adjunction.compUliftCoyonedaIso.{0} adj).symm.app (op X)) κ

Depends on / 依赖: Adjunction, Adjunction.compUliftCoyonedaIso, Functor, Functor.isCardinalAccessible_of_natIso, compUliftCoyonedaIso, isCardinalAccessible_of_natIso, isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj, symm.app
-/
lemma isCardinalPresentable_leftAdjoint_obj (X : C) [IsCardinalPresentable X κ]
    [G.IsCardinalAccessible κ] :
    IsCardinalPresentable (F.obj X) κ := by
  rw [isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj.{v}]
  exact Functor.isCardinalAccessible_of_natIso
    (show G ⋙ _ ≅ _ from (Adjunction.compUliftCoyonedaIso.{0} adj).symm.app (op X)) κ

variable {κ} in
/--
lemma `isCardinalFilteredGenerator` / 引理 `isCardinalFilteredGenerator`

English:
lemma isCardinalFilteredGenerator
  proof: by
    rintro Y ⟨X, hX, ⟨e⟩⟩
    have hX' := hP.le_isCardinalPresentable X hX
    rw [isCardinalPresentable_iff] at hX' ⊢
    have := adj.isCardinalPresentable_leftAdjoint_obj κ X
    exact isCardinalPresentable_of_iso e κ
  exists_colimitsOfShape Y := by
    have := adj.isLeftAdjoint
    obtain ⟨J,

中文:
引理 isCardinalFilteredGenerator
  证明: by
    rintro Y ⟨X, hX, ⟨e⟩⟩
    have hX' := hP.le_isCardinalPresentable X hX
    rw [isCardinalPresentable_iff] at hX' ⊢
    have := adj.isCardinalPresentable_leftAdjoint_obj κ X
    exact isCardinalPresentable_of_iso e κ
  exists_colimitsOfShape Y := by
    have := adj.isLeftAdjoint
    obtain ⟨J,

Depends on / 依赖: G.obj, ObjectProperty, ObjectProperty.prop_of_isIso, adj.counit.app, adj.isCardinalPresentable_leftAdjoint_obj, adj.isLeftAdjoint, counit, exists_colimitsOfShape, hP.exists_colimitsOfShape, hP.le_isCardinalPresentable, hY.isColimit, isCardinalPresentable_iff, isCardinalPresentable_leftAdjoint_obj, isCardinalPresentable_of_iso, isColimit, isColimitOfPreserves, isLeftAdjoint, le_isCardinalPresentable, prop_diag_obj, prop_of_isIso
-/
lemma isCardinalFilteredGenerator
    {P : ObjectProperty C} (hP : P.IsCardinalFilteredGenerator κ)
    [G.IsCardinalAccessible κ] [G.Full] [G.Faithful] :
    (P.map F).IsCardinalFilteredGenerator κ where
  le_isCardinalPresentable := by
    rintro Y ⟨X, hX, ⟨e⟩⟩
    have hX' := hP.le_isCardinalPresentable X hX
    rw [isCardinalPresentable_iff] at hX' ⊢
    have := adj.isCardinalPresentable_leftAdjoint_obj κ X
    exact isCardinalPresentable_of_iso e κ
  exists_colimitsOfShape Y := by
    have := adj.isLeftAdjoint
    obtain ⟨J, _, _, ⟨hY⟩⟩ := hP.exists_colimitsOfShape (G.obj Y)
    exact ⟨J, inferInstance, inferInstance,
      ObjectProperty.prop_of_isIso _ (adj.counit.app Y) ⟨{
        diag := _
        ι := _
        isColimit := isColimitOfPreserves F hY.isColimit
        prop_diag_obj j := P.prop_map_obj _ (hY.prop_diag_obj j) }⟩⟩

/--
lemma `hasCardinalFilteredGenerator` / 引理 `hasCardinalFilteredGenerator`

English:
lemma hasCardinalFilteredGenerator
  statement: [HasCardinalFilteredGenerator C κ]
  proof: locallySmall_of_faithful G
  exists_generator := by
    obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_generator C κ
    exact ⟨P.map F, inferInstance, adj.isCardinalFilteredGenerator hP⟩

中文:
引理 hasCardinalFilteredGenerator
  结论: [有CardinalFilteredGenerator C κ]
  证明: locallySmall_of_faithful G
  exists_generator := by
    obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_generator C κ
    exact ⟨P.map F, inferInstance, adj.isCardinalFilteredGenerator hP⟩

Depends on / 依赖: locallySmall_of_faithful
-/
lemma hasCardinalFilteredGenerator [HasCardinalFilteredGenerator C κ]
    [G.IsCardinalAccessible κ] [G.Full] [G.Faithful] :
    HasCardinalFilteredGenerator D κ where
  toLocallySmall := locallySmall_of_faithful G
  exists_generator := by
    obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_generator C κ
    exact ⟨P.map F, inferInstance, adj.isCardinalFilteredGenerator hP⟩

/--
lemma `isCardinalLocallyPresentable` / 引理 `isCardinalLocallyPresentable`

English:
lemma isCardinalLocallyPresentable
  statement: [IsCardinalLocallyPresentable C κ]
  proof: letI : Reflective G := ⟨_, adj⟩
    hasColimits_of_reflective G
  toHasCardinalFilteredGenerator := adj.hasCardinalFilteredGenerator κ

中文:
引理 isCardinalLocallyPresentable
  结论: [是CardinalLocallyPresentable C κ]
  证明: letI : Reflective G := ⟨_, adj⟩
    hasColimits_of_reflective G
  toHasCardinalFilteredGenerator := adj.hasCardinalFilteredGenerator κ

Depends on / 依赖: Reflective, adj.hasCardinalFilteredGenerator, hasCardinalFilteredGenerator, hasColimits_of_reflective, toHasCardinalFilteredGenerator
-/
lemma isCardinalLocallyPresentable [IsCardinalLocallyPresentable C κ]
    [G.IsCardinalAccessible κ] [G.Full] [G.Faithful] :
    IsCardinalLocallyPresentable D κ where
  toHasColimitsOfSize :=
    letI : Reflective G := ⟨_, adj⟩
    hasColimits_of_reflective G
  toHasCardinalFilteredGenerator := adj.hasCardinalFilteredGenerator κ

/--
lemma `isCardinalAccessibleCategory` / 引理 `isCardinalAccessibleCategory`

English:
lemma isCardinalAccessibleCategory
  statement: [IsCardinalAccessibleCategory C κ]
  proof: ⟨fun J _ _ =>
    let : Reflective G := ⟨_, adj⟩
    have := HasCardinalFilteredColimits.hasColimitsOfShape C κ J
    hasColimitsOfShape_of_reflective G⟩
  toHasCardinalFilteredGenerator := adj.hasCardinalFilteredGenerator κ

中文:
引理 isCardinalAccessibleCategory
  结论: [是CardinalAccessible范畴 C κ]
  证明: ⟨fun J _ _ =>
    let : Reflective G := ⟨_, adj⟩
    have := HasCardinalFilteredColimits.hasColimitsOfShape C κ J
    hasColimitsOfShape_of_reflective G⟩
  toHasCardinalFilteredGenerator := adj.hasCardinalFilteredGenerator κ
-/
lemma isCardinalAccessibleCategory [IsCardinalAccessibleCategory C κ]
    [G.IsCardinalAccessible κ] [G.Full] [G.Faithful] :
    IsCardinalAccessibleCategory D κ where
  toHasCardinalFilteredColimits := ⟨fun J _ _ =>
    let : Reflective G := ⟨_, adj⟩
    have := HasCardinalFilteredColimits.hasColimitsOfShape C κ J
    hasColimitsOfShape_of_reflective G⟩
  toHasCardinalFilteredGenerator := adj.hasCardinalFilteredGenerator κ

end Adjunction

namespace Equivalence

variable (e : C ≌ D)

include e

section

variable (κ : Cardinal.{w}) [Fact κ.IsRegular]

/--
lemma `hasCardinalFilteredGenerator` / 引理 `hasCardinalFilteredGenerator`

English:
lemma hasCardinalFilteredGenerator
  given: [HasCardinalFilteredGenerator C κ]
  proof: e.toAdjunction.hasCardinalFilteredGenerator κ

中文:
引理 hasCardinalFilteredGenerator
  条件: [有CardinalFilteredGenerator C κ]
  证明: e.toAdjunction.hasCardinalFilteredGenerator κ

Depends on / 依赖: e.toAdjunction.hasCardinalFilteredGenerator, hasCardinalFilteredGenerator, toAdjunction
-/
lemma hasCardinalFilteredGenerator [HasCardinalFilteredGenerator C κ] :
    HasCardinalFilteredGenerator D κ :=
  e.toAdjunction.hasCardinalFilteredGenerator κ

/--
lemma `isCardinalLocallyPresentable` / 引理 `isCardinalLocallyPresentable`

English:
lemma isCardinalLocallyPresentable
  given: [IsCardinalLocallyPresentable C κ]
  proof: e.toAdjunction.isCardinalLocallyPresentable κ

中文:
引理 isCardinalLocallyPresentable
  条件: [是CardinalLocallyPresentable C κ]
  证明: e.toAdjunction.isCardinalLocallyPresentable κ

Depends on / 依赖: e.toAdjunction.isCardinalLocallyPresentable, isCardinalLocallyPresentable, toAdjunction
-/
lemma isCardinalLocallyPresentable [IsCardinalLocallyPresentable C κ] :
    IsCardinalLocallyPresentable D κ :=
  e.toAdjunction.isCardinalLocallyPresentable κ

/--
lemma `isCardinalAccessibleCategory` / 引理 `isCardinalAccessibleCategory`

English:
lemma isCardinalAccessibleCategory
  given: [IsCardinalAccessibleCategory C κ]
  proof: e.toAdjunction.isCardinalAccessibleCategory κ

中文:
引理 isCardinalAccessibleCategory
  条件: [是CardinalAccessible范畴 C κ]
  证明: e.toAdjunction.isCardinalAccessibleCategory κ

Depends on / 依赖: e.toAdjunction.isCardinalAccessibleCategory, isCardinalAccessibleCategory, toAdjunction
-/
lemma isCardinalAccessibleCategory [IsCardinalAccessibleCategory C κ] :
    IsCardinalAccessibleCategory D κ :=
  e.toAdjunction.isCardinalAccessibleCategory κ

end

/--
lemma `isLocallyPresentable` / 引理 `isLocallyPresentable`

English:
lemma isLocallyPresentable
  given: [IsLocallyPresentable.{w} C]
  proof: by
  obtain ⟨κ, _, _⟩ := IsLocallyPresentable.exists_cardinal.{w} C
  exact ⟨κ, inferInstance, e.isCardinalLocallyPresentable κ⟩

中文:
引理 isLocallyPresentable
  条件: [是LocallyPresentable.{w} C]
  证明: by
  obtain ⟨κ, _, _⟩ := IsLocallyPresentable.exists_cardinal.{w} C
  exact ⟨κ, inferInstance, e.isCardinalLocallyPresentable κ⟩

Depends on / 依赖: IsLocallyPresentable, IsLocallyPresentable.exists_cardinal, e.isCardinalLocallyPresentable, exists_cardinal, isCardinalLocallyPresentable
-/
lemma isLocallyPresentable [IsLocallyPresentable.{w} C] :
    IsLocallyPresentable.{w} D := by
  obtain ⟨κ, _, _⟩ := IsLocallyPresentable.exists_cardinal.{w} C
  exact ⟨κ, inferInstance, e.isCardinalLocallyPresentable κ⟩

/--
lemma `isAccessibleCategory` / 引理 `isAccessibleCategory`

English:
lemma isAccessibleCategory
  given: [IsAccessibleCategory.{w} C]
  proof: by
  obtain ⟨κ, _, _⟩ := IsAccessibleCategory.exists_cardinal.{w} C
  exact ⟨κ, inferInstance, e.isCardinalAccessibleCategory κ⟩

中文:
引理 isAccessibleCategory
  条件: [是Accessible范畴.{w} C]
  证明: by
  obtain ⟨κ, _, _⟩ := IsAccessibleCategory.exists_cardinal.{w} C
  exact ⟨κ, inferInstance, e.isCardinalAccessibleCategory κ⟩

Depends on / 依赖: IsAccessibleCategory, IsAccessibleCategory.exists_cardinal, e.isCardinalAccessibleCategory, exists_cardinal, isCardinalAccessibleCategory
-/
lemma isAccessibleCategory [IsAccessibleCategory.{w} C] :
    IsAccessibleCategory.{w} D := by
  obtain ⟨κ, _, _⟩ := IsAccessibleCategory.exists_cardinal.{w} C
  exact ⟨κ, inferInstance, e.isCardinalAccessibleCategory κ⟩

end Equivalence

end CategoryTheory
