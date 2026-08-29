/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsCardinalClosure
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Functor.KanExtension.Dense
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-!
# Locally presentable categories and strong generators

In this file, we show that a category is locally `κ`-presentable iff
it is cocomplete and has a strong generator consisting of `κ`-presentable objects.
This is theorem 1.20 in the book by Adámek and Rosický.

In particular, if a category is locally `κ`-presentable, it is also
locally `κ'`-presentable for any regular cardinal `κ'` such that `κ ≤ κ'`.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

public section

universe w v' v u' u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

variable (κ) in
/--
lemma `IsCardinalFilteredGenerator.of_isDense` / 引理 `IsCardinalFilteredGenerator.of_isDense`

English:
lemma IsCardinalFilteredGenerator.of_isDense
  proof: by
    rintro X ⟨Y, hY, ⟨e⟩⟩
    exact isCardinalPresentable_of_iso e κ
  exists_colimitsOfShape X := by
    have ip := F.denseAt X
    let e := equivSmallModel.{w} (CostructuredArrow F X)
    exact ⟨SmallModel.{w} (CostructuredArrow F X), inferInstance,
      IsCardinalFiltered.of_equivalence κ e,


中文:
引理 IsCardinalFilteredGenerator.of_isDense
  证明: by
    rintro X ⟨Y, hY, ⟨e⟩⟩
    exact isCardinalPresentable_of_iso e κ
  exists_colimitsOfShape X := by
    have ip := F.denseAt X
    let e := equivSmallModel.{w} (CostructuredArrow F X)
    exact ⟨SmallModel.{w} (CostructuredArrow F X), inferInstance,
      IsCardinalFiltered.of_equivalence κ e,


Depends on / 依赖: CostructuredArrow, F.denseAt, IsCardinalFiltered, IsCardinalFiltered.of_equivalence, Iso.refl, SmallModel, denseAt, e.symm, equivSmallModel, exists_colimitsOfShape, isCardinalPresentable_of_iso, isColimit, of_equivalence, prop_diag_obj, whiskerEquivalence
-/
lemma IsCardinalFilteredGenerator.of_isDense
    [LocallySmall.{w} C] {J : Type u'} [Category.{v'} J] [EssentiallySmall.{w} J]
    (F : J ⥤ C) [F.IsDense] (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [forall j, IsCardinalPresentable (F.obj j) κ]
    [forall (X : C), IsCardinalFiltered (CostructuredArrow F X) κ] :
    ((⊤ : ObjectProperty J).map F).IsCardinalFilteredGenerator κ where
  le_isCardinalPresentable := by
    rintro X ⟨Y, hY, ⟨e⟩⟩
    exact isCardinalPresentable_of_iso e κ
  exists_colimitsOfShape X := by
    have ip := F.denseAt X
    let e := equivSmallModel.{w} (CostructuredArrow F X)
    exact ⟨SmallModel.{w} (CostructuredArrow F X), inferInstance,
      IsCardinalFiltered.of_equivalence κ e,
      ⟨{ diag := _
          ι := _
          isColimit := (F.denseAt X).whiskerEquivalence e.symm
          prop_diag_obj j := ⟨_, by simp, ⟨Iso.refl _⟩⟩ }⟩⟩

variable (κ) in
/--
lemma `IsCardinalFilteredGenerator.of_isDense_ι` / 引理 `IsCardinalFilteredGenerator.of_isDense_ι`

English:
lemma IsCardinalFilteredGenerator.of_isDense_ι
  proof: by
  rw [← ObjectProperty.IsCardinalFilteredGenerator.isoClosure_iff]
  have (X : P.FullSubcategory) : IsCardinalPresentable (P.ι.obj X) κ := hP _ X.property
  simpa using IsCardinalFilteredGenerator.of_isDense P.ι κ

中文:
引理 IsCardinalFilteredGenerator.of_isDense_ι
  证明: by
  rw [← ObjectProperty.IsCardinalFilteredGenerator.isoClosure_iff]
  have (X : P.FullSubcategory) : IsCardinalPresentable (P.ι.obj X) κ := hP _ X.property
  simpa using IsCardinalFilteredGenerator.of_isDense P.ι κ

Depends on / 依赖: FullSubcategory, IsCardinalFilteredGenerator, IsCardinalFilteredGenerator.of_isDense, IsCardinalPresentable, ObjectProperty, ObjectProperty.IsCardinalFilteredGenerator.isoClosure_iff, P.FullSubcategory, X.property, isoClosure_iff, of_isDense, property
-/
lemma IsCardinalFilteredGenerator.of_isDense_ι
    (P : ObjectProperty C) [ObjectProperty.EssentiallySmall.{w} P]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [P.ι.IsDense]
    [LocallySmall.{w} C]
    (hP : P <= isCardinalPresentable C κ)
    [forall (X : C), IsCardinalFiltered (CostructuredArrow P.ι X) κ] :
    P.IsCardinalFilteredGenerator κ := by
  rw [← ObjectProperty.IsCardinalFilteredGenerator.isoClosure_iff]
  have (X : P.FullSubcategory) : IsCardinalPresentable (P.ι.obj X) κ := hP _ X.property
  simpa using IsCardinalFilteredGenerator.of_isDense P.ι κ

/--
Instance `ObjectProperty.isCardinalFiltered_costructuredArrow_colimitsCardinalClosure_ι` / 实例 `ObjectProperty.isCardinalFiltered_costructuredArrow_colimitsCardinalClosure_ι`

English:
instance ObjectProperty.isCardinalFiltered_costructuredArrow_colimitsCardinalClosure_ι
  body: ⟨by
    have := ObjectProperty.isClosedUnderColimitsOfShape_colimitsCardinalClosure P κ J hJ
    exact colimit.cocone K⟩

中文:
实例 ObjectProperty.isCardinalFiltered_costructuredArrow_colimitsCardinalClosure_ι
  定义体: ⟨by
    have := ObjectProperty.isClosedUnderColimitsOfShape_colimitsCardinalClosure P κ J hJ
    exact colimit.cocone K⟩

Depends on / 依赖: ObjectProperty, ObjectProperty.isClosedUnderColimitsOfShape_colimitsCardinalClosure, cocone, colimit, colimit.cocone, isClosedUnderColimitsOfShape_colimitsCardinalClosure
-/
instance ObjectProperty.isCardinalFiltered_costructuredArrow_colimitsCardinalClosure_ι
    (P : ObjectProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [HasColimitsOfSize.{w, w} C] (X : C) :
    IsCardinalFiltered (CostructuredArrow (P.colimitsCardinalClosure κ).ι X) κ where
  nonempty_cocone {J} _ K hJ := ⟨by
    have := ObjectProperty.isClosedUnderColimitsOfShape_colimitsCardinalClosure P κ J hJ
    exact colimit.cocone K⟩

/--
Instance `ObjectProperty.isFiltered_costructuredArrow_colimitsCardinalClosure_ι` / 实例 `ObjectProperty.isFiltered_costructuredArrow_colimitsCardinalClosure_ι`

English:
instance ObjectProperty.isFiltered_costructuredArrow_colimitsCardinalClosure_ι
  body: isFiltered_of_isCardinalFiltered _ κ

中文:
实例 ObjectProperty.isFiltered_costructuredArrow_colimitsCardinalClosure_ι
  定义体: isFiltered_of_isCardinalFiltered _ κ

Depends on / 依赖: isFiltered_of_isCardinalFiltered
-/
instance ObjectProperty.isFiltered_costructuredArrow_colimitsCardinalClosure_ι
    (P : ObjectProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [HasColimitsOfSize.{w, w} C] (X : C) :
    IsFiltered (CostructuredArrow (P.colimitsCardinalClosure κ).ι X) :=
  isFiltered_of_isCardinalFiltered _ κ

variable {κ : Cardinal.{w}} [Fact κ.IsRegular]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `ObjectProperty.IsStrongGenerator.isDense_colimitsCardinalClosure_ι` / 引理 `ObjectProperty.IsStrongGenerator.isDense_colimitsCardinalClosure_ι`

English:
lemma ObjectProperty.IsStrongGenerator.isDense_colimitsCardinalClosure_ι
  proof: by
    let E := Functor.LeftExtension.mk _ (P.colimitsCardinalClosure κ).ι.rightUnitor.inv
    have : HasColimitsOfShape (CostructuredArrow (P.colimitsCardinalClosure κ).ι X) C :=
      hasColimitsOfShape_of_equivalence
        (equivSmallModel.{w} (CostructuredArrow (P.colimitsCardinalClosure κ).ι 

中文:
引理 ObjectProperty.IsStrongGenerator.isDense_colimitsCardinalClosure_ι
  证明: by
    let E := Functor.LeftExtension.mk _ (P.colimitsCardinalClosure κ).ι.rightUnitor.inv
    have : HasColimitsOfShape (CostructuredArrow (P.colimitsCardinalClosure κ).ι X) C :=
      hasColimitsOfShape_of_equivalence
        (equivSmallModel.{w} (CostructuredArrow (P.colimitsCardinalClosure κ).ι 

Depends on / 依赖: CostructuredArrow, CostructuredArrow.proj, E.coconeAt, Functor, Functor.LeftExtension.mk, HasColimitsOfShape, LeftExtension, P.colimitsCardinalClosure, coconeAt, colimit, colimit.desc, colimitsCardinalClosure, equivSmallModel, hasColimitsOfShape_of_equivalence, isSeparating, isSeparating.mono_iff, mono_iff, rightUnitor, rightUnitor.inv
-/
lemma ObjectProperty.IsStrongGenerator.isDense_colimitsCardinalClosure_ι
    [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C]
    {P : ObjectProperty C} [ObjectProperty.Small.{w} P] (hS₁ : P.IsStrongGenerator)
    (hS₂ : P <= isCardinalPresentable C κ) :
    (P.colimitsCardinalClosure κ).ι.IsDense where
  isDenseAt X := by
    let E := Functor.LeftExtension.mk _ (P.colimitsCardinalClosure κ).ι.rightUnitor.inv
    have : HasColimitsOfShape (CostructuredArrow (P.colimitsCardinalClosure κ).ι X) C :=
      hasColimitsOfShape_of_equivalence
        (equivSmallModel.{w} (CostructuredArrow (P.colimitsCardinalClosure κ).ι X)).symm
    have : Mono (colimit.desc _ (E.coconeAt X)) := by
      let Φ := CostructuredArrow.proj (P.colimitsCardinalClosure κ).ι X ⋙
        (P.colimitsCardinalClosure κ).ι
      rw [hS₁.isSeparating.mono_iff]
      intro G hG (g₁ : G ⟶ colimit Φ) (g₂ : G ⟶ colimit Φ)
        (h : g₁ ≫ colimit.desc Φ (E.coconeAt X) = g₂ ≫ colimit.desc Φ (E.coconeAt X))
      have : IsCardinalPresentable G κ := hS₂ _ hG
      obtain ⟨j, φ₁, φ₂, rfl, rfl⟩ :
          exists (j : CostructuredArrow (P.colimitsCardinalClosure κ).ι X)
            (φ₁ φ₂ : G ⟶ Φ.obj j), φ₁ ≫ colimit.ι _ _ = g₁ ∧ φ₂ ≫ colimit.ι _ _ = g₂ := by
        obtain ⟨j₁, f₁, hf₁⟩ :=
          IsCardinalPresentable.exists_hom_of_isColimit κ (colimit.isColimit _) g₁
        obtain ⟨j₂, f₂, hf₂⟩ :=
          IsCardinalPresentable.exists_hom_of_isColimit κ (colimit.isColimit _) g₂
        exact ⟨IsFiltered.max j₁ j₂, f₁ ≫ Φ.map (IsFiltered.leftToMax j₁ j₂),
          f₂ ≫ Φ.map (IsFiltered.rightToMax j₁ j₂), by simpa, by simpa⟩
      have : (P.colimitsCardinalClosure κ).IsClosedUnderColimitsOfShape WalkingParallelPair := by
        apply ObjectProperty.isClosedUnderColimitsOfShape_colimitsCardinalClosure
        refine .of_le ?_ (Cardinal.IsRegular.aleph0_le Fact.out)
        simp only [hasCardinalLT_aleph0_iff]
        infer_instance
      let obj : (P.colimitsCardinalClosure κ).FullSubcategory :=
        ⟨coequalizer φ₁ φ₂, by
          apply ObjectProperty.prop_colimit
          rintro (_ | _)
          · exact P.le_colimitsCardinalClosure _ _ hG
          · exact j.left.2⟩
      let a : (P.colimitsCardinalClosure κ).ι.obj obj ⟶ X :=
        coequalizer.desc ((E.coconeAt X).ι.app j) (by simpa using h)
      let ψ : j ⟶ CostructuredArrow.mk a :=
        CostructuredArrow.homMk (ObjectProperty.homMk (coequalizer.π _ _)) (by simp [E, a])
      rw [← colimit.w Φ ψ]
      apply coequalizer.condition_assoc
    have : IsIso (colimit.desc _ (E.coconeAt X)) := hS₁.isIso_of_mono _ (fun Y hY g => by
      let γ : CostructuredArrow (P.colimitsCardinalClosure κ).ι X :=
        CostructuredArrow.mk (Y := ⟨Y, P.le_colimitsCardinalClosure _ _ hY⟩) (by exact g)
      exact ⟨colimit.ι (CostructuredArrow.proj _ _ ⋙ (P.colimitsCardinalClosure κ).ι) γ,
        by simp [γ, E]⟩)
    exact ⟨IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext
      (asIso (colimit.desc _ (E.coconeAt X))))⟩

/--
lemma `ObjectProperty.colimitsCardinalClosure_le_isCardinalPresentable` / 引理 `ObjectProperty.colimitsCardinalClosure_le_isCardinalPresentable`

English:
lemma ObjectProperty.colimitsCardinalClosure_le_isCardinalPresentable
  proof: P.colimitsCardinalClosure_le κ
    (fun _ _ hJ => isClosedUnderColimitsOfShape_isCardinalPresentable C hJ) hP

中文:
引理 ObjectProperty.colimitsCardinalClosure_le_isCardinalPresentable
  证明: P.colimitsCardinalClosure_le κ
    (fun _ _ hJ => isClosedUnderColimitsOfShape_isCardinalPresentable C hJ) hP

Depends on / 依赖: P.colimitsCardinalClosure_le, colimitsCardinalClosure_le, isClosedUnderColimitsOfShape_isCardinalPresentable
-/
lemma ObjectProperty.colimitsCardinalClosure_le_isCardinalPresentable
    [LocallySmall.{w} C] (P : ObjectProperty C) (hP : P <= isCardinalPresentable C κ) :
    P.colimitsCardinalClosure κ <= isCardinalPresentable C κ :=
  P.colimitsCardinalClosure_le κ
    (fun _ _ hJ => isClosedUnderColimitsOfShape_isCardinalPresentable C hJ) hP

/--
lemma `IsStrongGenerator.colimitsCardinalClosure_eq_isCardinalPresentable` / 引理 `IsStrongGenerator.colimitsCardinalClosure_eq_isCardinalPresentable`

English:
lemma IsStrongGenerator.colimitsCardinalClosure_eq_isCardinalPresentable
  proof: by
  refine le_antisymm ?_ (P.colimitsCardinalClosure_le_isCardinalPresentable hS₂)
  have := hS₁.isDense_colimitsCardinalClosure_ι hS₂
  intro X hX
  rw [isCardinalPresentable_iff] at hX
  rw [← (P.colimitsCardinalClosure κ).retractClosure_eq_self]
  obtain ⟨j, φ, hφ⟩ := IsCardinalPresentable.exist

中文:
引理 IsStrongGenerator.colimitsCardinalClosure_eq_isCardinalPresentable
  证明: by
  refine le_antisymm ?_ (P.colimitsCardinalClosure_le_isCardinalPresentable hS₂)
  have := hS₁.isDense_colimitsCardinalClosure_ι hS₂
  intro X hX
  rw [isCardinalPresentable_iff] at hX
  rw [← (P.colimitsCardinalClosure κ).retractClosure_eq_self]
  obtain ⟨j, φ, hφ⟩ := IsCardinalPresentable.exist

Depends on / 依赖: IsCardinalPresentable, IsCardinalPresentable.exists_hom_of_isColimit, P.colimitsCardinalClosure, P.colimitsCardinalClosure_le_isCardinalPresentable, colimitsCardinalClosure, colimitsCardinalClosure_le_isCardinalPresentable, denseAt, exists_hom_of_isColimit, isCardinalPresentable_iff, j.left, le_antisymm, retract, retractClosure_eq_self
-/
lemma IsStrongGenerator.colimitsCardinalClosure_eq_isCardinalPresentable
    [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C]
    {P : ObjectProperty C} [ObjectProperty.Small.{w} P] (hS₁ : P.IsStrongGenerator)
    (hS₂ : P <= isCardinalPresentable C κ) :
    isCardinalPresentable C κ = P.colimitsCardinalClosure κ := by
  refine le_antisymm ?_ (P.colimitsCardinalClosure_le_isCardinalPresentable hS₂)
  have := hS₁.isDense_colimitsCardinalClosure_ι hS₂
  intro X hX
  rw [isCardinalPresentable_iff] at hX
  rw [← (P.colimitsCardinalClosure κ).retractClosure_eq_self]
  obtain ⟨j, φ, hφ⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ
    ((P.colimitsCardinalClosure κ).ι.denseAt X) (𝟙 X)
  exact ⟨_, j.left.2, ⟨{ i := _, r := _, retract := hφ }⟩⟩

namespace IsCardinalLocallyPresentable

variable (C κ) in
/--
lemma `iff_exists_isStrongGenerator` / 引理 `iff_exists_isStrongGenerator`

English:
lemma iff_exists_isStrongGenerator
  given: [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C]
  proof: by
  refine ⟨fun _ => ?_, fun ⟨P, _, hS₁, hS₂⟩ => ?_⟩
  · obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_small_generator C κ
    exact ⟨_, inferInstance, hP.isStrongGenerator, hP.le_isCardinalPresentable⟩
  · have := hS₁.isDense_colimitsCardinalClosure_ι hS₂
    have : HasCardinalFilteredG

中文:
引理 iff_exists_isStrongGenerator
  条件: [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C]
  证明: by
  refine ⟨fun _ => ?_, fun ⟨P, _, hS₁, hS₂⟩ => ?_⟩
  · obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_small_generator C κ
    exact ⟨_, inferInstance, hP.isStrongGenerator, hP.le_isCardinalPresentable⟩
  · have := hS₁.isDense_colimitsCardinalClosure_ι hS₂
    have : HasCardinalFilteredG

Depends on / 依赖: HasCardinalFilteredGenerator, HasCardinalFilteredGenerator.exists_small_generator, IsCardinalFilteredGenerator, IsCardinalFilteredGenerator.of_isDense_, P.colimitsCardinalClosure, P.colimitsCardinalClosure_le_isCardinalPresentable, colimitsCardinalClosure, colimitsCardinalClosure_le_isCardinalPresentable, exists_generator, exists_small_generator, hP.isStrongGenerator, hP.le_isCardinalPresentable, isStrongGenerator, le_isCardinalPresentable
-/
lemma iff_exists_isStrongGenerator [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C] :
    IsCardinalLocallyPresentable C κ ↔
      exists (P : ObjectProperty C) (_ : ObjectProperty.Small.{w} P), P.IsStrongGenerator ∧
        P <= isCardinalPresentable C κ := by
  refine ⟨fun _ => ?_, fun ⟨P, _, hS₁, hS₂⟩ => ?_⟩
  · obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_small_generator C κ
    exact ⟨_, inferInstance, hP.isStrongGenerator, hP.le_isCardinalPresentable⟩
  · have := hS₁.isDense_colimitsCardinalClosure_ι hS₂
    have : HasCardinalFilteredGenerator C κ :=
      { exists_generator := ⟨(P.colimitsCardinalClosure κ), inferInstance,
            IsCardinalFilteredGenerator.of_isDense_ι _ _
              (P.colimitsCardinalClosure_le_isCardinalPresentable hS₂)⟩ }
    constructor

variable (C) in
/--
lemma `of_le` / 引理 `of_le`

English:
lemma of_le
  statement: [IsCardinalLocallyPresentable C κ] {κ' : Cardinal.{w}} [Fact κ'.IsRegular]
  proof: by
  rw [iff_exists_isStrongGenerator]
  obtain ⟨S, _, h₁, h₂⟩ := (iff_exists_isStrongGenerator C κ).1 inferInstance
  exact ⟨S, inferInstance, h₁, h₂.trans (isCardinalPresentable_monotone _ h)⟩

中文:
引理 of_le
  结论: [IsCardinalLocallyPresentable C κ] {κ' : Cardinal.{w}} [Fact κ'.IsRegular]
  证明: by
  rw [iff_exists_isStrongGenerator]
  obtain ⟨S, _, h₁, h₂⟩ := (iff_exists_isStrongGenerator C κ).1 inferInstance
  exact ⟨S, inferInstance, h₁, h₂.trans (isCardinalPresentable_monotone _ h)⟩

Depends on / 依赖: iff_exists_isStrongGenerator, isCardinalPresentable_monotone
-/
lemma of_le [IsCardinalLocallyPresentable C κ] {κ' : Cardinal.{w}} [Fact κ'.IsRegular]
    (h : κ <= κ') :
    IsCardinalLocallyPresentable C κ' := by
  rw [iff_exists_isStrongGenerator]
  obtain ⟨S, _, h₁, h₂⟩ := (iff_exists_isStrongGenerator C κ).1 inferInstance
  exact ⟨S, inferInstance, h₁, h₂.trans (isCardinalPresentable_monotone _ h)⟩

end IsCardinalLocallyPresentable

end CategoryTheory
