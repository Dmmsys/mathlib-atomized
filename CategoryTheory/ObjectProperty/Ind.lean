/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Presentable.ColimitPresentation
public import Mathlib.CategoryTheory.Presentable.Dense
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct

/-!
# Ind and pro-properties

Given an object property `P`, we define an object property `ind P` that is satisfied for
`X` if `X` is a filtered colimit of `Xᵢ` and `Xᵢ` satisfies `P`.

## Main definitions

- `CategoryTheory.ObjectProperty.ind`: `X` satisfies `ind P` if `X` is a filtered colimit of `Xᵢ`
  for `Xᵢ` in `P`.

## Main results

- `CategoryTheory.ObjectProperty.ind_ind`: If `P` implies finitely presentable, then
  `P.ind.ind = P.ind`.

## TODOs:

- Dualise to obtain `CategoryTheory.ObjectProperty.pro`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.ObjectProperty

open Limits Opposite

variable {C : Type u} [Category.{v} C] {P : ObjectProperty C}

/--
Definition of `ind` / `ind` 的定义

English:
definition ind
  signature: (P : ObjectProperty C)
  body: fun X => exists (J : Type w) (_ : SmallCategory J) (_ : IsFiltered J)
    (pres : ColimitPresentation J X), forall i, P (pres.diag.obj i)

中文:
定义 ind
  签名: (P : ObjectProperty C)
  定义体: fun X => exists (J : Type w) (_ : SmallCategory J) (_ : IsFiltered J)
    (pres : ColimitPresentation J X), forall i, P (pres.diag.obj i)

Depends on / 依赖: ColimitPresentation, IsFiltered, PUnit.unit, SmallCategory, cat_disch, pres.diag.obj
-/
def ind (P : ObjectProperty C) : ObjectProperty C :=
  fun X => exists (J : Type w) (_ : SmallCategory J) (_ : IsFiltered J)
    (pres : ColimitPresentation J X), forall i, P (pres.diag.obj i)

variable (P) in
/--
lemma `le_ind` / 引理 `le_ind`

English:
lemma le_ind
  statement: P <= ind.{w} P
  proof: by
  intro X hX
  exact ⟨PUnit, inferInstance, inferInstance, .self X, by simpa⟩

中文:
引理 le_ind
  结论: P <= ind.{w} P
  证明: by
  intro X hX
  exact ⟨PUnit, inferInstance, inferInstance, .self X, by simpa⟩
-/
lemma le_ind : P <= ind.{w} P := by
  intro X hX
  exact ⟨PUnit, inferInstance, inferInstance, .self X, by simpa⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.Nonempty]
  signature: : (ind.{w} P).Nonempty
  body: .mono P.le_ind

中文:
实例 [P.非空]
  签名: : (ind.{w} P).非空
  定义体: .mono P.le_ind

Depends on / 依赖: P.le_ind, le_ind
-/
instance [P.Nonempty] : (ind.{w} P).Nonempty := .mono P.le_ind

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.ind.IsClosedUnderIsomorphisms
  body: fun ⟨J, _, _, pres, h⟩ => ⟨J, ‹_›, ‹_›, pres.ofIso e, h⟩

中文:
实例 :
  签名: P.ind.在同构下封闭
  定义体: fun ⟨J, _, _, pres, h⟩ => ⟨J, ‹_›, ‹_›, pres.ofIso e, h⟩

Depends on / 依赖: pres.ofIso
-/
instance : P.ind.IsClosedUnderIsomorphisms where
  of_iso {X Y} e := fun ⟨J, _, _, pres, h⟩ => ⟨J, ‹_›, ‹_›, pres.ofIso e, h⟩

/--
lemma `ind_ind` / 引理 `ind_ind`

English:
lemma ind_ind
  given: (h : P <= isFinitelyPresentable.{w} C) [LocallySmall.{w} C]
  proof: by
  refine le_antisymm (fun X h => ?_) (le_ind P.ind)
  choose J Jc Jf pres K Kc Kf pres' hp using h
  have (j : J) (i : K j) : IsFinitelyPresentable ((pres' j).diag.obj i) := h _ (hp _ _)
  have := IsFiltered.of_equivalence (ShrinkHoms.equivalence (ColimitPresentation.Total pres'))
  exact ⟨_, inf

中文:
引理 ind_ind
  条件: (h : P <= isFinitelyPresentable.{w} C) [LocallySmall.{w} C]
  证明: by
  refine le_antisymm (fun X h => ?_) (le_ind P.ind)
  choose J Jc Jf pres K Kc Kf pres' hp using h
  have (j : J) (i : K j) : IsFinitelyPresentable ((pres' j).diag.obj i) := h _ (hp _ _)
  have := IsFiltered.of_equivalence (ShrinkHoms.equivalence (ColimitPresentation.Total pres'))
  exact ⟨_, inf

Depends on / 依赖: ColimitPresentation, ColimitPresentation.Total, IsFiltered, IsFiltered.of_equivalence, IsFinitelyPresentable, P.ind, ShrinkHoms, ShrinkHoms.equivalence, diag.obj, equivalence, inverse, le_antisymm, le_ind, of_equivalence, pres.bind, reindex
-/
lemma ind_ind (h : P <= isFinitelyPresentable.{w} C) [LocallySmall.{w} C] :
    ind.{w} (ind.{w} P) = ind.{w} P := by
  refine le_antisymm (fun X h => ?_) (le_ind P.ind)
  choose J Jc Jf pres K Kc Kf pres' hp using h
  have (j : J) (i : K j) : IsFinitelyPresentable ((pres' j).diag.obj i) := h _ (hp _ _)
  have := IsFiltered.of_equivalence (ShrinkHoms.equivalence (ColimitPresentation.Total pres'))
  exact ⟨_, inferInstance, inferInstance,
    (pres.bind pres').reindex (ShrinkHoms.equivalence _).inverse, fun k => by simp [hp]⟩

/--
lemma `of_essentiallySmall_index` / 引理 `of_essentiallySmall_index`

English:
lemma of_essentiallySmall_index
  statement: {X : C} {J : Type*} [Category* J] [EssentiallySmall.{w} J]
  proof: ⟨SmallModel J, inferInstance, .of_equivalence (equivSmallModel _),
    pres.reindex (equivSmallModel _).inverse, fun _ => h _⟩

中文:
引理 of_essentiallySmall_index
  结论: {X : C} {J : 类型} [范畴* J] [EssentiallySmall.{w} J]
  证明: ⟨SmallModel J, inferInstance, .of_equivalence (equivSmallModel _),
    pres.reindex (equivSmallModel _).inverse, fun _ => h _⟩

Depends on / 依赖: SmallModel, equivSmallModel, inverse, of_equivalence, pres.reindex, reindex
-/
lemma of_essentiallySmall_index {X : C} {J : Type*} [Category* J] [EssentiallySmall.{w} J]
    [IsFiltered J] (pres : ColimitPresentation J X) (h : forall i, P (pres.diag.obj i)) :
    ind.{w} P X :=
  ⟨SmallModel J, inferInstance, .of_equivalence (equivSmallModel _),
    pres.reindex (equivSmallModel _).inverse, fun _ => h _⟩

/--
lemma `ind_iff_exists` / 引理 `ind_iff_exists`

English:
lemma ind_iff_exists
  statement: (H : P <= isFinitelyPresentable.{w} C)
  proof: by
  refine ⟨fun ⟨J, _, _, pres, h⟩ Z g hZ => ?_, fun hfac => ?_⟩
  · have : IsFinitelyPresentable Z := hZ
    obtain ⟨j, u, hcomp⟩ := IsFinitelyPresentable.exists_hom_of_isColimit pres.isColimit g
    exact ⟨_, u, pres.ι.app j, hcomp, h j⟩
  · let incl : P.FullSubcategory ⥤ (isFinitelyPresentable.{

中文:
引理 ind_iff_存在
  结论: (H : P <= isFinitelyPresentable.{w} C)
  证明: by
  refine ⟨fun ⟨J, _, _, pres, h⟩ Z g hZ => ?_, fun hfac => ?_⟩
  · have : IsFinitelyPresentable Z := hZ
    obtain ⟨j, u, hcomp⟩ := IsFinitelyPresentable.exists_hom_of_isColimit pres.isColimit g
    exact ⟨_, u, pres.ι.app j, hcomp, h j⟩
  · let incl : P.FullSubcategory ⥤ (isFinitelyPresentable.{

Depends on / 依赖: CostructuredArrow, CostructuredArrow.pre, FullSubcategory, IsFinitelyPresentable, IsFinitelyPresentable.exists_hom_of_isColimit, Nonempty, ObjectProperty, P.FullSubcategory, exists_hom_of_isColimit, isColimit, isFinitelyPresentable, pres.isColimit
-/
lemma ind_iff_exists (H : P <= isFinitelyPresentable.{w} C)
    [IsFinitelyAccessibleCategory.{w} C] {X : C} :
    ind.{w} P X ↔ forall {Z : C} (g : Z ⟶ X) [IsFinitelyPresentable.{w} Z],
      exists (W : C) (u : Z ⟶ W) (v : W ⟶ X), u ≫ v = g ∧ P W := by
  refine ⟨fun ⟨J, _, _, pres, h⟩ Z g hZ => ?_, fun hfac => ?_⟩
  · have : IsFinitelyPresentable Z := hZ
    obtain ⟨j, u, hcomp⟩ := IsFinitelyPresentable.exists_hom_of_isColimit pres.isColimit g
    exact ⟨_, u, pres.ι.app j, hcomp, h j⟩
  · let incl : P.FullSubcategory ⥤ (isFinitelyPresentable.{w} C).FullSubcategory :=
      ObjectProperty.ιOfLE H
    have H (d : CostructuredArrow (isFinitelyPresentable.{w} C).ι X) : exists c,
        Nonempty (d ⟶ (CostructuredArrow.pre incl (isFinitelyPresentable.{w} C).ι X).obj c) := by
      obtain ⟨W, u, v, huv, hW⟩ := hfac d.hom
      exact ⟨CostructuredArrow.mk (Y := FullSubcategory.mk _ hW) v,
        ⟨CostructuredArrow.homMk ⟨u⟩ huv⟩⟩
    have : (CostructuredArrow.pre incl (isFinitelyPresentable.{w} C).ι X).Final :=
      Functor.final_of_exists_of_isFiltered_of_fullyFaithful (C := CostructuredArrow (incl ⋙ _) X)
        (CostructuredArrow.pre incl (isFinitelyPresentable.{w} C).ι X) H
    have : IsFiltered (CostructuredArrow P.ι X) :=
      .of_exists_of_isFiltered_of_fullyFaithful (C := CostructuredArrow (incl ⋙ _) X)
        (CostructuredArrow.pre incl (isFinitelyPresentable.{w} C).ι X) H
    obtain ⟨hc⟩ : P.ι.isDenseAt X :=
      Functor.IsDenseAt.of_final (F := (isFinitelyPresentable.{w} C).ι) incl
        (Functor.IsDense.isDenseAt _ _)
    have : EssentiallySmall.{w} (CostructuredArrow P.ι X) :=
      essentiallySmall_of_fully_faithful (C := CostructuredArrow (incl ⋙ _) X)
        (CostructuredArrow.pre incl (isFinitelyPresentable.{w} C).ι X)
    exact of_essentiallySmall_index ⟨_, _, hc⟩ fun Y => Y.left.2

section

variable {D : Type*} [Category D] (P : ObjectProperty D) (F : C ⥤ D)

/--
lemma `ind_inverseImage_le` / 引理 `ind_inverseImage_le`

English:
lemma ind_inverseImage_le
  given: [PreservesFilteredColimitsOfSize.{w, w} F]
  proof: by
  intro X ⟨J, _, _, pres, h⟩
  simp only [prop_inverseImage_iff]
  use J, inferInstance, inferInstance, pres.map F, h

中文:
引理 ind_inverseImage_le
  条件: [保持FilteredColimitsOfSize.{w, w} F]
  证明: by
  intro X ⟨J, _, _, pres, h⟩
  simp only [prop_inverseImage_iff]
  use J, inferInstance, inferInstance, pres.map F, h

Depends on / 依赖: pres.map, prop_inverseImage_iff
-/
lemma ind_inverseImage_le [PreservesFilteredColimitsOfSize.{w, w} F] :
    ind.{w} (P.inverseImage F) <= (ind.{w} P).inverseImage F := by
  intro X ⟨J, _, _, pres, h⟩
  simp only [prop_inverseImage_iff]
  use J, inferInstance, inferInstance, pres.map F, h

/--
lemma `ind_inverseImage_eq_of_isEquivalence` / 引理 `ind_inverseImage_eq_of_isEquivalence`

English:
lemma ind_inverseImage_eq_of_isEquivalence
  given: [P.IsClosedUnderIsomorphisms] [F.IsEquivalence]
  proof: by
  refine le_antisymm (ind_inverseImage_le _ _) fun X ⟨J, _, _, pres, h⟩ => ?_
  refine ⟨J, ‹_›, ‹_›, .ofIso (pres.map F.asEquivalence.inverse) ?_, fun j => ?_⟩
  · exact (F.asEquivalence.unitIso.app X).symm
  · exact P.prop_of_iso ((F.asEquivalence.counitIso.app _).symm) (h j)

中文:
引理 ind_inverseImage_eq_of_isEquivalence
  条件: [P.在同构下封闭] [F.是等价]
  证明: by
  refine le_antisymm (ind_inverseImage_le _ _) fun X ⟨J, _, _, pres, h⟩ => ?_
  refine ⟨J, ‹_›, ‹_›, .ofIso (pres.map F.asEquivalence.inverse) ?_, fun j => ?_⟩
  · exact (F.asEquivalence.unitIso.app X).symm
  · exact P.prop_of_iso ((F.asEquivalence.counitIso.app _).symm) (h j)

Depends on / 依赖: F.asEquivalence.counitIso.app, F.asEquivalence.inverse, F.asEquivalence.unitIso.app, P.prop_of_iso, asEquivalence, counitIso, ind_inverseImage_le, inverse, le_antisymm, pres.map, prop_of_iso, unitIso
-/
lemma ind_inverseImage_eq_of_isEquivalence [P.IsClosedUnderIsomorphisms] [F.IsEquivalence] :
    ind.{w} (P.inverseImage F) = (ind.{w} P).inverseImage F := by
  refine le_antisymm (ind_inverseImage_le _ _) fun X ⟨J, _, _, pres, h⟩ => ?_
  refine ⟨J, ‹_›, ‹_›, .ofIso (pres.map F.asEquivalence.inverse) ?_, fun j => ?_⟩
  · exact (F.asEquivalence.unitIso.app X).symm
  · exact P.prop_of_iso ((F.asEquivalence.counitIso.app _).symm) (h j)

/--
lemma `ind_iff_of_equivalence` / 引理 `ind_iff_of_equivalence`

English:
lemma ind_iff_of_equivalence
  given: (e : C ≌ D) [P.IsClosedUnderIsomorphisms] (X : D)
  proof: by
  dsimp only [ObjectProperty.ind]
  congr!
  refine ⟨fun ⟨pres, h⟩ => ?_, fun ⟨pres, h⟩ => ?_⟩
  · exact ⟨.ofIso (pres.map e.functor) (e.counitIso.app X), fun i => h i⟩
  · exact ⟨pres.map e.inverse, fun i => P.prop_of_iso ((e.counitIso.app _).symm) (h i)⟩

中文:
引理 ind_iff_of_equivalence
  条件: (e : C ≌ D) [P.在同构下封闭] (X : D)
  证明: by
  dsimp only [ObjectProperty.ind]
  congr!
  refine ⟨fun ⟨pres, h⟩ => ?_, fun ⟨pres, h⟩ => ?_⟩
  · exact ⟨.ofIso (pres.map e.functor) (e.counitIso.app X), fun i => h i⟩
  · exact ⟨pres.map e.inverse, fun i => P.prop_of_iso ((e.counitIso.app _).symm) (h i)⟩

Depends on / 依赖: ObjectProperty, ObjectProperty.ind, P.prop_of_iso, counitIso, e.counitIso.app, e.functor, e.inverse, functor, inverse, pres.map, prop_of_iso
-/
lemma ind_iff_of_equivalence (e : C ≌ D) [P.IsClosedUnderIsomorphisms] (X : D) :
    ind.{w} (P.inverseImage e.functor) (e.inverse.obj X) ↔ ind.{w} P X := by
  dsimp only [ObjectProperty.ind]
  congr!
  refine ⟨fun ⟨pres, h⟩ => ?_, fun ⟨pres, h⟩ => ?_⟩
  · exact ⟨.ofIso (pres.map e.functor) (e.counitIso.app X), fun i => h i⟩
  · exact ⟨pres.map e.inverse, fun i => P.prop_of_iso ((e.counitIso.app _).symm) (h i)⟩

end

section Products

/--
lemma `ind_pi_of_ind` / 引理 `ind_pi_of_ind`

English:
lemma ind_pi_of_ind
  statement: {ι : Type w} [P.IsClosedUnderLimitsOfShape (Discrete ι)]
  proof: by
  choose J _ _ pres hpres using hc
  obtain ⟨hc⟩ := IsIPCOfShape.nonempty_isColimit fun i => (pres i).isColimit
  exact ⟨forall j, J j, inferInstance, inferInstance,
    { diag := _, ι := _, isColimit := hc }, fun i => P.prop_limit _ fun a => hpres a.1 _⟩

中文:
引理 ind_pi_of_ind
  结论: {ι : 类型 w} [P.是ClosedUnderLimitsOfShape (离散 ι)]
  证明: by
  choose J _ _ pres hpres using hc
  obtain ⟨hc⟩ := IsIPCOfShape.nonempty_isColimit fun i => (pres i).isColimit
  exact ⟨forall j, J j, inferInstance, inferInstance,
    { diag := _, ι := _, isColimit := hc }, fun i => P.prop_limit _ fun a => hpres a.1 _⟩
-/
private lemma ind_pi_of_ind {ι : Type w} [P.IsClosedUnderLimitsOfShape (Discrete ι)]
    [HasProductsOfShape ι C] [IsIPCOfShape.{w} ι C] {X : ι -> C} (hc : forall i, ind.{w} P (X i)) :
    ind.{w} P (∏ᶜ X) := by
  choose J _ _ pres hpres using hc
  obtain ⟨hc⟩ := IsIPCOfShape.nonempty_isColimit fun i => (pres i).isColimit
  exact ⟨forall j, J j, inferInstance, inferInstance,
    { diag := _, ι := _, isColimit := hc }, fun i => P.prop_limit _ fun a => hpres a.1 _⟩

/--
Instance `isClosedUnderLimitsOfShape_ind_discrete` / 实例 `isClosedUnderLimitsOfShape_ind_discrete`

English:
instance isClosedUnderLimitsOfShape_ind_discrete
  signature: {ι : Type*} [Small.{w} ι]
  body: by
  refine .mk' fun X ⟨Y, h⟩ => ?_
  let e := equivShrink ι
  have : HasProductsOfShape (Shrink.{w} ι) C :=
    hasLimitsOfShape_of_equivalence (Discrete.equivalence e)
  have : IsIPCOfShape.{w} (Shrink.{w} ι) C := .of_equiv e
  have : P.IsClosedUnderLimitsOfShape (Discrete (Shrink.{w} ι)) :=
    .

中文:
实例 isClosedUnderLimitsOfShape_ind_discrete
  签名: {ι : 类型} [Small.{w} ι]
  定义体: by
  refine .mk' fun X ⟨Y, h⟩ => ?_
  let e := equivShrink ι
  have : HasProductsOfShape (Shrink.{w} ι) C :=
    hasLimitsOfShape_of_equivalence (Discrete.equivalence e)
  have : IsIPCOfShape.{w} (Shrink.{w} ι) C := .of_equiv e
  have : P.IsClosedUnderLimitsOfShape (Discrete (Shrink.{w} ι)) :=
    .

Depends on / 依赖: Discrete, Discrete.equivalence, HasProductsOfShape, IsClosedUnderLimitsOfShape, IsIPCOfShape, P.IsClosedUnderLimitsOfShape, Pi.isoLimit, Pi.reindex, Shrink, Y.obj, e.symm, equivShrink, equivalence, hasLimitsOfShape_of_equivalence, ind_pi_of_ind, isoLimit, of_equiv, of_equivalence, prop_iff_of_iso, reindex
-/
instance isClosedUnderLimitsOfShape_ind_discrete {ι : Type*} [Small.{w} ι]
    [P.IsClosedUnderLimitsOfShape (Discrete ι)] [HasProductsOfShape ι C] [IsIPCOfShape.{w} ι C] :
    (ind.{w} P).IsClosedUnderLimitsOfShape (Discrete ι) := by
  refine .mk' fun X ⟨Y, h⟩ => ?_
  let e := equivShrink ι
  have : HasProductsOfShape (Shrink.{w} ι) C :=
    hasLimitsOfShape_of_equivalence (Discrete.equivalence e)
  have : IsIPCOfShape.{w} (Shrink.{w} ι) C := .of_equiv e
  have : P.IsClosedUnderLimitsOfShape (Discrete (Shrink.{w} ι)) :=
    .of_equivalence (Discrete.equivalence e)
  let iso : limit Y ≅ ∏ᶜ fun i => Y.obj ⟨e.symm i⟩ :=
    (Pi.isoLimit _).symm ≪≫ (Pi.reindex e.symm _).symm
  rw [(ind.{w} P).prop_iff_of_iso iso]
  exact ind_pi_of_ind fun i => h _

end Products

end CategoryTheory.ObjectProperty
