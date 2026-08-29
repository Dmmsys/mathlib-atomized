/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# (Co)limits in subcategories of comma categories defined by morphism properties

-/

@[expose] public section

namespace CategoryTheory

open Limits MorphismProperty.Comma

variable {T : Type*} [Category* T] (P : MorphismProperty T)

namespace MorphismProperty.Comma

variable {A B J : Type*} [Category* A] [Category* B] [Category* J] {L : A ⥤ T} {R : B ⥤ T}
variable (D : J ⥤ P.Comma L R ⊤ ⊤)

/-- If `P` is closed under limits of shape `J` in `Comma L R`, then when `D` has
a limit in `Comma L R`, the forgetful functor creates this limit. -/
@[instance_reducible]
/--
Definition of `forgetCreatesLimitOfClosed` / `forgetCreatesLimitOfClosed` 的定义

English:
definition forgetCreatesLimitOfClosed
  body: createsLimitOfFullyFaithfulOfIso
    (⟨limit (D ⋙ forget L R P ⊤ ⊤),
      ObjectProperty.prop_limit (P.commaObj L R) _
        fun j => (D.obj j).prop⟩) (Iso.refl _)

中文:
定义 forgetCreatesLimitOfClosed
  定义体: createsLimitOfFullyFaithfulOfIso
    (⟨limit (D ⋙ forget L R P ⊤ ⊤),
      ObjectProperty.prop_limit (P.commaObj L R) _
        fun j => (D.obj j).prop⟩) (Iso.refl _)

Depends on / 依赖: D.obj, Iso.refl, ObjectProperty, ObjectProperty.prop_limit, P.commaObj, commaObj, createsLimitOfFullyFaithfulOfIso, forget, prop_limit
-/
noncomputable def forgetCreatesLimitOfClosed
    [(P.commaObj L R).IsClosedUnderLimitsOfShape J]
    [HasLimit (D ⋙ forget L R P ⊤ ⊤)] :
    CreatesLimit D (forget L R P ⊤ ⊤) :=
  createsLimitOfFullyFaithfulOfIso
    (⟨limit (D ⋙ forget L R P ⊤ ⊤),
      ObjectProperty.prop_limit (P.commaObj L R) _
        fun j => (D.obj j).prop⟩) (Iso.refl _)

/-- If `Comma L R` has limits of shape `J` and `Comma L R` is closed under limits of shape
`J`, then `forget L R P ⊤ ⊤` creates limits of shape `J`. -/
@[instance_reducible]
/--
Definition of `forgetCreatesLimitsOfShapeOfClosed` / `forgetCreatesLimitsOfShapeOfClosed` 的定义

English:
definition forgetCreatesLimitsOfShapeOfClosed
  signature: [HasLimitsOfShape J (Comma L R)]
  body: forgetCreatesLimitOfClosed _ _

中文:
定义 forgetCreatesLimitsOfShapeOfClosed
  签名: [有形状极限 J (交换a L R)]
  定义体: forgetCreatesLimitOfClosed _ _

Depends on / 依赖: forgetCreatesLimitOfClosed
-/
noncomputable def forgetCreatesLimitsOfShapeOfClosed [HasLimitsOfShape J (Comma L R)]
    [ObjectProperty.IsClosedUnderLimitsOfShape (P.commaObj L R) J] :
    CreatesLimitsOfShape J (forget L R P ⊤ ⊤) where
  CreatesLimit := forgetCreatesLimitOfClosed _ _

/--
lemma `hasLimit_of_closedUnderLimitsOfShape` / 引理 `hasLimit_of_closedUnderLimitsOfShape`

English:
lemma hasLimit_of_closedUnderLimitsOfShape
  proof: haveI : CreatesLimit D (forget L R P ⊤ ⊤) := forgetCreatesLimitOfClosed _ D
  hasLimit_of_created D (forget L R P ⊤ ⊤)

中文:
引理 hasLimit_of_closedUnderLimitsOfShape
  证明: haveI : CreatesLimit D (forget L R P ⊤ ⊤) := forgetCreatesLimitOfClosed _ D
  hasLimit_of_created D (forget L R P ⊤ ⊤)

Depends on / 依赖: CreatesLimit, forget, forgetCreatesLimitOfClosed, hasLimit_of_created
-/
lemma hasLimit_of_closedUnderLimitsOfShape
    [(P.commaObj L R).IsClosedUnderLimitsOfShape J]
    [HasLimit (D ⋙ forget L R P ⊤ ⊤)] :
    HasLimit D :=
  haveI : CreatesLimit D (forget L R P ⊤ ⊤) := forgetCreatesLimitOfClosed _ D
  hasLimit_of_created D (forget L R P ⊤ ⊤)

/--
Instance `hasLimitsOfShape_of_closedUnderLimitsOfShape` / 实例 `hasLimitsOfShape_of_closedUnderLimitsOfShape`

English:
instance hasLimitsOfShape_of_closedUnderLimitsOfShape
  signature: [HasLimitsOfShape J (Comma L R)]
  body: hasLimit_of_closedUnderLimitsOfShape _ _

中文:
实例 hasLimitsOfShape_of_closedUnderLimitsOfShape
  签名: [有形状极限 J (交换a L R)]
  定义体: hasLimit_of_closedUnderLimitsOfShape _ _

Depends on / 依赖: hasLimit_of_closedUnderLimitsOfShape
-/
instance hasLimitsOfShape_of_closedUnderLimitsOfShape [HasLimitsOfShape J (Comma L R)]
    [(P.commaObj L R).IsClosedUnderLimitsOfShape J] :
    HasLimitsOfShape J (P.Comma L R ⊤ ⊤) where
  has_limit _ := hasLimit_of_closedUnderLimitsOfShape _ _

/-- If `P` is closed under colimits of shape `J` in `Comma L R`, then when `D` has
a colimit in `Comma L R`, the forgetful functor creates this colimit. -/
@[instance_reducible]
/--
Definition of `forgetCreatesColimitOfClosed` / `forgetCreatesColimitOfClosed` 的定义

English:
definition forgetCreatesColimitOfClosed
  body: createsColimitOfFullyFaithfulOfIso
    (⟨colimit (D ⋙ forget L R P ⊤ ⊤),
      (P.commaObj L R).prop_colimit _ (fun j => (D.obj j).prop)⟩) (Iso.refl _)

中文:
定义 forgetCreatesColimitOfClosed
  定义体: createsColimitOfFullyFaithfulOfIso
    (⟨colimit (D ⋙ forget L R P ⊤ ⊤),
      (P.commaObj L R).prop_colimit _ (fun j => (D.obj j).prop)⟩) (Iso.refl _)

Depends on / 依赖: D.obj, Iso.refl, P.commaObj, colimit, commaObj, createsColimitOfFullyFaithfulOfIso, forget, prop_colimit
-/
noncomputable def forgetCreatesColimitOfClosed
    [(P.commaObj L R).IsClosedUnderColimitsOfShape J]
    [HasColimit (D ⋙ forget L R P ⊤ ⊤)] :
    CreatesColimit D (forget L R P ⊤ ⊤) :=
  createsColimitOfFullyFaithfulOfIso
    (⟨colimit (D ⋙ forget L R P ⊤ ⊤),
      (P.commaObj L R).prop_colimit _ (fun j => (D.obj j).prop)⟩) (Iso.refl _)

variable (J) in
/-- If `Comma L R` has colimits of shape `J` and `Comma L R` is closed under colimits of shape
`J`, then `forget L R P ⊤ ⊤` creates colimits of shape `J`. -/
@[instance_reducible]
/--
Definition of `forgetCreatesColimitsOfShapeOfClosed` / `forgetCreatesColimitsOfShapeOfClosed` 的定义

English:
definition forgetCreatesColimitsOfShapeOfClosed
  signature: [HasColimitsOfShape J (Comma L R)]
  body: forgetCreatesColimitOfClosed _ _

中文:
定义 forgetCreatesColimitsOfShapeOfClosed
  签名: [有形状余极限 J (交换a L R)]
  定义体: forgetCreatesColimitOfClosed _ _

Depends on / 依赖: forgetCreatesColimitOfClosed
-/
noncomputable def forgetCreatesColimitsOfShapeOfClosed [HasColimitsOfShape J (Comma L R)]
    [(P.commaObj L R).IsClosedUnderColimitsOfShape J] :
    CreatesColimitsOfShape J (forget L R P ⊤ ⊤) where
  CreatesColimit := forgetCreatesColimitOfClosed _ _

/--
lemma `hasColimit_of_closedUnderColimitsOfShape` / 引理 `hasColimit_of_closedUnderColimitsOfShape`

English:
lemma hasColimit_of_closedUnderColimitsOfShape
  proof: haveI : CreatesColimit D (forget L R P ⊤ ⊤) := forgetCreatesColimitOfClosed _ D
  hasColimit_of_created D (forget L R P ⊤ ⊤)

中文:
引理 hasColimit_of_closedUnderColimitsOfShape
  证明: haveI : CreatesColimit D (forget L R P ⊤ ⊤) := forgetCreatesColimitOfClosed _ D
  hasColimit_of_created D (forget L R P ⊤ ⊤)

Depends on / 依赖: CreatesColimit, forget, forgetCreatesColimitOfClosed, hasColimit_of_created
-/
lemma hasColimit_of_closedUnderColimitsOfShape
    [(P.commaObj L R).IsClosedUnderColimitsOfShape J]
    [HasColimit (D ⋙ forget L R P ⊤ ⊤)] :
    HasColimit D :=
  haveI : CreatesColimit D (forget L R P ⊤ ⊤) := forgetCreatesColimitOfClosed _ D
  hasColimit_of_created D (forget L R P ⊤ ⊤)

/--
Instance `hasColimitsOfShape_of_closedUnderColimitsOfShape` / 实例 `hasColimitsOfShape_of_closedUnderColimitsOfShape`

English:
instance hasColimitsOfShape_of_closedUnderColimitsOfShape
  signature: [HasColimitsOfShape J (Comma L R)]
  body: hasColimit_of_closedUnderColimitsOfShape _ _

中文:
实例 hasColimitsOfShape_of_closedUnderColimitsOfShape
  签名: [有形状余极限 J (交换a L R)]
  定义体: hasColimit_of_closedUnderColimitsOfShape _ _

Depends on / 依赖: hasColimit_of_closedUnderColimitsOfShape
-/
instance hasColimitsOfShape_of_closedUnderColimitsOfShape [HasColimitsOfShape J (Comma L R)]
    [(P.commaObj L R).IsClosedUnderColimitsOfShape J] :
    HasColimitsOfShape J (P.Comma L R ⊤ ⊤) where
  has_colimit _ := hasColimit_of_closedUnderColimitsOfShape _ _

end MorphismProperty.Comma

section CostructuredArrow

variable {A : Type*} [Category* A] {L : A ⥤ T}

/--
Instance `CostructuredArrow.closedUnderLimitsOfShape_discrete_empty` / 实例 `CostructuredArrow.closedUnderLimitsOfShape_discrete_empty`

English:
instance CostructuredArrow.closedUnderLimitsOfShape_discrete_empty
  signature: [L.Faithful] [L.Full] {Y : A}
  body: by
    rintro X p
    let t : IsTerminal X := (ObjectProperty.limitsOfShape_isEmpty_iff _ _ _ |>.mp p).some
    let e : X ≅ CostructuredArrow.mk (𝟙 (L.obj Y)) := t.uniqueUpToIso CostructuredArrow.mkIdTerminal
    simpa [MorphismProperty.costructuredArrowObj_iff,
      P.costructuredArrow_iso_iff e] using P.id_mem (L.obj Y)

中文:
实例 CostructuredArrow.closedUnderLimitsOfShape_discrete_empty
  签名: [L.忠实] [L.满] {Y : A}
  定义体: by
    rintro X p
    let t : IsTerminal X := (ObjectProperty.limitsOfShape_isEmpty_iff _ _ _ |>.mp p).some
    let e : X ≅ CostructuredArrow.mk (𝟙 (L.obj Y)) := t.uniqueUpToIso CostructuredArrow.mkIdTerminal
    simpa [MorphismProperty.costructuredArrowObj_iff,
      P.costructuredArrow_iso_iff e] using P.id_mem (L.obj Y)

Depends on / 依赖: Discrete, IsClosedUnderLimitsOfShape, L.obj, PEmpty
-/
instance CostructuredArrow.closedUnderLimitsOfShape_discrete_empty [L.Faithful] [L.Full] {Y : A}
    [P.ContainsIdentities] [P.RespectsIso] :
    (P.costructuredArrowObj L (X := L.obj Y)).IsClosedUnderLimitsOfShape (Discrete PEmpty.{1}) where
  limitsOfShape_le := by
    rintro X p
    let t : IsTerminal X := (ObjectProperty.limitsOfShape_isEmpty_iff _ _ _ |>.mp p).some
    let e : X ≅ CostructuredArrow.mk (𝟙 (L.obj Y)) := t.uniqueUpToIso CostructuredArrow.mkIdTerminal
    simpa [MorphismProperty.costructuredArrowObj_iff,
      P.costructuredArrow_iso_iff e] using P.id_mem (L.obj Y)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `CostructuredArrow.isClosedUnderColimitsOfShape` / 引理 `CostructuredArrow.isClosedUnderColimitsOfShape`

English:
lemma CostructuredArrow.isClosedUnderColimitsOfShape
  statement: {J : Type*} [Category* J]
  proof: by
    intro ⟨d⟩
    let hd : IsColimit ((CategoryTheory.CostructuredArrow.proj L X ⋙ L).mapCocone d.cocone) :=
      isColimitOfPreserves _ d.isColimit
    have heq : Y.hom = hd.desc { pt := X, ι := { app j := (d.diag.obj j).hom } } := by
      refine hd.hom_ext fun j => ?_
      simp only [IsColimit.fac]
      simp
    rw [P.costructuredArrowObj_iff]; rw [heq]; rw [← hd.coconePointUniqueUpToIso_hom_desc (hc _)]; rw [P.cancel_left_of_respectsIso]
    exact H _ _ d.prop_diag_obj

中文:
引理 CostructuredArrow.isClosedUnderColimitsOfShape
  结论: {J : 类型} [范畴* J]
  证明: by
    intro ⟨d⟩
    let hd : IsColimit ((CategoryTheory.CostructuredArrow.proj L X ⋙ L).mapCocone d.cocone) :=
      isColimitOfPreserves _ d.isColimit
    have heq : Y.hom = hd.desc { pt := X, ι := { app j := (d.diag.obj j).hom } } := by
      refine hd.hom_ext fun j => ?_
      simp only [IsColimit.fac]
      simp
    rw [P.costructuredArrowObj_iff]; rw [heq]; rw [← hd.coconePointUniqueUpToIso_hom_desc (hc _)]; rw [P.cancel_left_of_respectsIso]
    exact H _ _ d.prop_diag_obj

Depends on / 依赖: IsClosedUnderColimitsOfShape
-/
lemma CostructuredArrow.isClosedUnderColimitsOfShape {J : Type*} [Category* J]
    {P : MorphismProperty T} [P.RespectsIso] [PreservesColimitsOfShape J L] [HasColimitsOfShape J A]
    (c : forall (D : J ⥤ T) [HasColimit D], Cocone D)
    (hc : forall (D : J ⥤ T) [HasColimit D], IsColimit (c D))
    (H : forall (D : J ⥤ T) [HasColimit D] {X : T} (s : D ⟶ (Functor.const J).obj X),
      (forall j, P (s.app j)) -> P ((hc D).desc (Cocone.mk X s))) (X : T) :
    (P.costructuredArrowObj L (X := X)).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le Y := by
    intro ⟨d⟩
    let hd : IsColimit ((CategoryTheory.CostructuredArrow.proj L X ⋙ L).mapCocone d.cocone) :=
      isColimitOfPreserves _ d.isColimit
    have heq : Y.hom = hd.desc { pt := X, ι := { app j := (d.diag.obj j).hom } } := by
      refine hd.hom_ext fun j => ?_
      simp only [IsColimit.fac]
      simp
    rw [P.costructuredArrowObj_iff]; rw [heq]; rw [← hd.coconePointUniqueUpToIso_hom_desc (hc _)]; rw [P.cancel_left_of_respectsIso]
    exact H _ _ d.prop_diag_obj

set_option backward.defeqAttrib.useBackward true in
/--
lemma `CostructuredArrow.closedUnderLimitsOfShape_walkingCospan` / 引理 `CostructuredArrow.closedUnderLimitsOfShape_walkingCospan`

English:
lemma CostructuredArrow.closedUnderLimitsOfShape_walkingCospan
  statement: [HasPullbacks A] [HasPullbacks T]
  proof: by
    rintro Y ⟨pres, hpres⟩
    have h : IsPullback (L.map (pres.π.app .left).left) (L.map (pres.π.app .right).left)
        (L.map (pres.diag.map WalkingCospan.Hom.inl).left)
          (L.map (pres.diag.map WalkingCospan.Hom.inr).left) :=
IsPullback.of_isLimit_cone isLimitOfPreserves
        (CategoryTheory.CostructuredArrow.toOver L X ⋙ CategoryTheory.Over.forget X) pres.isLimit
    rw [MorphismProperty.costructuredArrowObj_iff]
    rw [show Y.hom = L.map (pres.π.app .left).left ≫ (pres.diag.obj .left).hom by simp]
    apply P.comp_mem _ _ (P.of_isPullback h.flip ?_) (hpres _)
    exact P.of_postcomp _ (pres.diag.obj WalkingCospan.one).hom (hpres .one)
      (by simpa using hpres .right)

中文:
引理 CostructuredArrow.closedUnderLimitsOfShape_walkingCospan
  结论: [有Pullbacks A] [有Pullbacks T]
  证明: by
    rintro Y ⟨pres, hpres⟩
    have h : IsPullback (L.map (pres.π.app .left).left) (L.map (pres.π.app .right).left)
        (L.map (pres.diag.map WalkingCospan.Hom.inl).left)
          (L.map (pres.diag.map WalkingCospan.Hom.inr).left) :=
IsPullback.of_isLimit_cone isLimitOfPreserves
        (CategoryTheory.CostructuredArrow.toOver L X ⋙ CategoryTheory.Over.forget X) pres.isLimit
    rw [MorphismProperty.costructuredArrowObj_iff]
    rw [show Y.hom = L.map (pres.π.app .left).left ≫ (pres.diag.obj .left).hom by simp]
    apply P.comp_mem _ _ (P.of_isPullback h.flip ?_) (hpres _)
    exact P.of_postcomp _ (pres.diag.obj WalkingCospan.one).hom (hpres .one)
      (by simpa using hpres .right)

Depends on / 依赖: IsClosedUnderLimitsOfShape, WalkingCospan
-/
lemma CostructuredArrow.closedUnderLimitsOfShape_walkingCospan [HasPullbacks A] [HasPullbacks T]
    [PreservesLimitsOfShape WalkingCospan L] (X : T)
    [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
    [P.HasOfPostcompProperty P] :
    (P.costructuredArrowObj L (X := X)).IsClosedUnderLimitsOfShape WalkingCospan where
  limitsOfShape_le := by
    rintro Y ⟨pres, hpres⟩
    have h : IsPullback (L.map (pres.π.app .left).left) (L.map (pres.π.app .right).left)
        (L.map (pres.diag.map WalkingCospan.Hom.inl).left)
          (L.map (pres.diag.map WalkingCospan.Hom.inr).left) :=
IsPullback.of_isLimit_cone isLimitOfPreserves
        (CategoryTheory.CostructuredArrow.toOver L X ⋙ CategoryTheory.Over.forget X) pres.isLimit
    rw [MorphismProperty.costructuredArrowObj_iff]
    rw [show Y.hom = L.map (pres.π.app .left).left ≫ (pres.diag.obj .left).hom by simp]
    apply P.comp_mem _ _ (P.of_isPullback h.flip ?_) (hpres _)
    exact P.of_postcomp _ (pres.diag.obj WalkingCospan.one).hom (hpres .one)
      (by simpa using hpres .right)

namespace MorphismProperty.CostructuredArrow

variable (X : T) [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
  [P.HasOfPostcompProperty P] [HasPullbacks A] [HasPullbacks T]
  [PreservesLimitsOfShape WalkingCospan L]

/--
Instance `createsLimitsOfShape_walkingCospan` / 实例 `createsLimitsOfShape_walkingCospan`

English:
instance createsLimitsOfShape_walkingCospan
  signature: :
  body: by
  apply +allowSynthFailures forgetCreatesLimitsOfShapeOfClosed
  · exact inferInstanceAs (HasLimitsOfShape WalkingCospan (CostructuredArrow L X))
  · exact CostructuredArrow.closedUnderLimitsOfShape_walkingCospan _ _

中文:
实例 createsLimitsOfShape_walkingCospan
  签名: :
  定义体: by
  apply +allowSynthFailures forgetCreatesLimitsOfShapeOfClosed
  · exact inferInstanceAs (HasLimitsOfShape WalkingCospan (CostructuredArrow L X))
  · exact CostructuredArrow.closedUnderLimitsOfShape_walkingCospan _ _

Depends on / 依赖: CostructuredArrow, CostructuredArrow.closedUnderLimitsOfShape_walkingCospan, HasLimitsOfShape, WalkingCospan, allowSynthFailures, closedUnderLimitsOfShape_walkingCospan, forgetCreatesLimitsOfShapeOfClosed
-/
noncomputable instance createsLimitsOfShape_walkingCospan :
    CreatesLimitsOfShape WalkingCospan (CostructuredArrow.forget P ⊤ L X) := by
  apply +allowSynthFailures forgetCreatesLimitsOfShapeOfClosed
  · exact inferInstanceAs (HasLimitsOfShape WalkingCospan (CostructuredArrow L X))
  · exact CostructuredArrow.closedUnderLimitsOfShape_walkingCospan _ _

/--
Instance `hasPullbacks` / 实例 `hasPullbacks`

English:
instance hasPullbacks
  signature: : HasPullbacks (P.CostructuredArrow ⊤ L X)
  body: by
  apply +allowSynthFailures hasLimitsOfShape_of_closedUnderLimitsOfShape
  · exact inferInstanceAs (HasLimitsOfShape WalkingCospan (CostructuredArrow L X))
  · exact CostructuredArrow.closedUnderLimitsOfShape_walkingCospan _ _

中文:
实例 hasPullbacks
  签名: : 有Pullbacks (P.CostructuredArrow ⊤ L X)
  定义体: by
  apply +allowSynthFailures hasLimitsOfShape_of_closedUnderLimitsOfShape
  · exact inferInstanceAs (HasLimitsOfShape WalkingCospan (CostructuredArrow L X))
  · exact CostructuredArrow.closedUnderLimitsOfShape_walkingCospan _ _

Depends on / 依赖: CostructuredArrow, CostructuredArrow.closedUnderLimitsOfShape_walkingCospan, HasLimitsOfShape, WalkingCospan, allowSynthFailures, closedUnderLimitsOfShape_walkingCospan, hasLimitsOfShape_of_closedUnderLimitsOfShape
-/
instance hasPullbacks : HasPullbacks (P.CostructuredArrow ⊤ L X) := by
  apply +allowSynthFailures hasLimitsOfShape_of_closedUnderLimitsOfShape
  · exact inferInstanceAs (HasLimitsOfShape WalkingCospan (CostructuredArrow L X))
  · exact CostructuredArrow.closedUnderLimitsOfShape_walkingCospan _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimitsOfShape WalkingCospan (CostructuredArrow.toOver P L X)
  body: have : PreservesLimitsOfShape WalkingCospan
      (CostructuredArrow.toOver P L X ⋙ Over.forget P ⊤ X) :=
inferInstanceAs PreservesLimitsOfShape WalkingCospan
      CostructuredArrow.forget P ⊤ L X ⋙ CategoryTheory.CostructuredArrow.toOver L X
  preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget _ _ X)

中文:
实例 :
  签名: 保持形状极限 WalkingCospan (CostructuredArrow.toOver P L X)
  定义体: have : PreservesLimitsOfShape WalkingCospan
      (CostructuredArrow.toOver P L X ⋙ Over.forget P ⊤ X) :=
inferInstanceAs PreservesLimitsOfShape WalkingCospan
      CostructuredArrow.forget P ⊤ L X ⋙ CategoryTheory.CostructuredArrow.toOver L X
  preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget _ _ X)

Depends on / 依赖: CategoryTheory, CategoryTheory.CostructuredArrow.toOver, CostructuredArrow, CostructuredArrow.forget, CostructuredArrow.toOver, Over.forget, PreservesLimitsOfShape, WalkingCospan, forget, preservesLimitsOfShape_of_reflects_of_preserves, toOver
-/
instance : PreservesLimitsOfShape WalkingCospan (CostructuredArrow.toOver P L X) :=
  have : PreservesLimitsOfShape WalkingCospan
      (CostructuredArrow.toOver P L X ⋙ Over.forget P ⊤ X) :=
inferInstanceAs PreservesLimitsOfShape WalkingCospan
      CostructuredArrow.forget P ⊤ L X ⋙ CategoryTheory.CostructuredArrow.toOver L X
  preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget _ _ X)

end MorphismProperty.CostructuredArrow

end CostructuredArrow

section

variable {A : Type*} [Category* A] {L : A ⥤ T}

/--
Instance `StructuredArrow.closedUnderColimitsOfShape_discrete_empty` / 实例 `StructuredArrow.closedUnderColimitsOfShape_discrete_empty`

English:
instance StructuredArrow.closedUnderColimitsOfShape_discrete_empty
  signature: [L.Faithful] [L.Full] {Y : A}
  body: by
    rintro X p
    let t : IsInitial X := (ObjectProperty.colimitsOfShape_isEmpty_iff _ _ _ |>.mp p).some
    let e : X ≅ StructuredArrow.mk (𝟙 (L.obj Y)) := t.uniqueUpToIso StructuredArrow.mkIdInitial
    simpa [MorphismProperty.structuredArrowObj_iff,
      P.structuredArrow_iso_iff e] using P.id_mem (L.obj Y)

中文:
实例 结构化箭头.closedUnderColimitsOfShape_discrete_empty
  签名: [L.忠实] [L.满] {Y : A}
  定义体: by
    rintro X p
    let t : IsInitial X := (ObjectProperty.colimitsOfShape_isEmpty_iff _ _ _ |>.mp p).some
    let e : X ≅ StructuredArrow.mk (𝟙 (L.obj Y)) := t.uniqueUpToIso StructuredArrow.mkIdInitial
    simpa [MorphismProperty.structuredArrowObj_iff,
      P.structuredArrow_iso_iff e] using P.id_mem (L.obj Y)

Depends on / 依赖: Discrete, IsClosedUnderColimitsOfShape, L.obj, PEmpty
-/
instance StructuredArrow.closedUnderColimitsOfShape_discrete_empty [L.Faithful] [L.Full] {Y : A}
    [P.ContainsIdentities] [P.RespectsIso] :
    (P.structuredArrowObj L (X := L.obj Y)).IsClosedUnderColimitsOfShape (Discrete PEmpty.{1}) where
  colimitsOfShape_le := by
    rintro X p
    let t : IsInitial X := (ObjectProperty.colimitsOfShape_isEmpty_iff _ _ _ |>.mp p).some
    let e : X ≅ StructuredArrow.mk (𝟙 (L.obj Y)) := t.uniqueUpToIso StructuredArrow.mkIdInitial
    simpa [MorphismProperty.structuredArrowObj_iff,
      P.structuredArrow_iso_iff e] using P.id_mem (L.obj Y)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `StructuredArrow.isClosedUnderLimitsOfShape` / 引理 `StructuredArrow.isClosedUnderLimitsOfShape`

English:
lemma StructuredArrow.isClosedUnderLimitsOfShape
  statement: {J : Type*} [Category* J]
  proof: by
    intro ⟨d⟩
    let hd : IsLimit ((CategoryTheory.StructuredArrow.proj X L ⋙ L).mapCone d.cone) :=
      isLimitOfPreserves _ d.isLimit
    have heq : Y.hom = hd.lift { pt := X, π := { app j := (d.diag.obj j).hom } } := by
      refine hd.hom_ext fun j => ?_
      simp only [IsLimit.fac]
      simp
    rw [P.structuredArrowObj_iff]; rw [heq]; rw [← (hc _).lift_comp_conePointUniqueUpToIso_hom hd]; rw [P.cancel_right_of_respectsIso]
    exact H _ _ d.prop_diag_obj

中文:
引理 结构化箭头.isClosedUnderLimitsOfShape
  结论: {J : 类型} [范畴* J]
  证明: by
    intro ⟨d⟩
    let hd : IsLimit ((CategoryTheory.StructuredArrow.proj X L ⋙ L).mapCone d.cone) :=
      isLimitOfPreserves _ d.isLimit
    have heq : Y.hom = hd.lift { pt := X, π := { app j := (d.diag.obj j).hom } } := by
      refine hd.hom_ext fun j => ?_
      simp only [IsLimit.fac]
      simp
    rw [P.structuredArrowObj_iff]; rw [heq]; rw [← (hc _).lift_comp_conePointUniqueUpToIso_hom hd]; rw [P.cancel_right_of_respectsIso]
    exact H _ _ d.prop_diag_obj

Depends on / 依赖: IsClosedUnderLimitsOfShape
-/
lemma StructuredArrow.isClosedUnderLimitsOfShape {J : Type*} [Category* J]
    {P : MorphismProperty T} [P.RespectsIso] [PreservesLimitsOfShape J L] [HasLimitsOfShape J A]
    (c : forall (D : J ⥤ T) [HasLimit D], Cone D)
    (hc : forall (D : J ⥤ T) [HasLimit D], IsLimit (c D))
    (H : forall (D : J ⥤ T) [HasLimit D] {X : T} (s : (Functor.const J).obj X ⟶ D),
      (forall j, P (s.app j)) -> P ((hc D).lift (Cone.mk X s))) (X : T) :
    (P.structuredArrowObj L (X := X)).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le Y := by
    intro ⟨d⟩
    let hd : IsLimit ((CategoryTheory.StructuredArrow.proj X L ⋙ L).mapCone d.cone) :=
      isLimitOfPreserves _ d.isLimit
    have heq : Y.hom = hd.lift { pt := X, π := { app j := (d.diag.obj j).hom } } := by
      refine hd.hom_ext fun j => ?_
      simp only [IsLimit.fac]
      simp
    rw [P.structuredArrowObj_iff]; rw [heq]; rw [← (hc _).lift_comp_conePointUniqueUpToIso_hom hd]; rw [P.cancel_right_of_respectsIso]
    exact H _ _ d.prop_diag_obj

end

section

variable {X : T}

/--
Instance `Over.closedUnderLimitsOfShape_discrete_empty` / 实例 `Over.closedUnderLimitsOfShape_discrete_empty`

English:
instance Over.closedUnderLimitsOfShape_discrete_empty
  signature: [P.ContainsIdentities] [P.RespectsIso]
  body: CostructuredArrow.closedUnderLimitsOfShape_discrete_empty P

中文:
实例 Over.closedUnderLimitsOfShape_discrete_empty
  签名: [P.余ntainsIdentities] [P.RespectsIso]
  定义体: CostructuredArrow.closedUnderLimitsOfShape_discrete_empty P

Depends on / 依赖: Discrete, IsClosedUnderLimitsOfShape, PEmpty
-/
instance Over.closedUnderLimitsOfShape_discrete_empty [P.ContainsIdentities] [P.RespectsIso] :
    (P.overObj (X := X)).IsClosedUnderLimitsOfShape (Discrete PEmpty.{1}) :=
  CostructuredArrow.closedUnderLimitsOfShape_discrete_empty P

set_option backward.defeqAttrib.useBackward true in
/--
Instance `Over.closedUnderLimitsOfShape_pullback` / 实例 `Over.closedUnderLimitsOfShape_pullback`

English:
instance Over.closedUnderLimitsOfShape_pullback
  signature: [HasPullbacks T]
  body: CostructuredArrow.closedUnderLimitsOfShape_walkingCospan _ _

中文:
实例 Over.closedUnderLimitsOfShape_pullback
  签名: [有Pullbacks T]
  定义体: CostructuredArrow.closedUnderLimitsOfShape_walkingCospan _ _

Depends on / 依赖: Functor, Functor.Monoidal.map_tensor, IsClosedUnderLimitsOfShape, Monoidal, MorphismProperty, MorphismProperty.RespectsIso.postcomp, MorphismProperty.RespectsIso.precomp, RespectsIso, WalkingCospan, inverseImage_iff, map_tensor, postcomp, precomp, tensorHom_mem
-/
instance Over.closedUnderLimitsOfShape_pullback [HasPullbacks T]
    [P.IsStableUnderComposition] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    (P.overObj (X := X)).IsClosedUnderLimitsOfShape WalkingCospan :=
  CostructuredArrow.closedUnderLimitsOfShape_walkingCospan _ _

end

section

variable {X : T}

/--
Instance `Under.closedUnderColimitsOfShape_discrete_empty` / 实例 `Under.closedUnderColimitsOfShape_discrete_empty`

English:
instance Under.closedUnderColimitsOfShape_discrete_empty
  signature: [P.ContainsIdentities] [P.RespectsIso]
  body: StructuredArrow.closedUnderColimitsOfShape_discrete_empty (L := 𝟭 _) P

中文:
实例 Under.closedUnderColimitsOfShape_discrete_empty
  签名: [P.余ntainsIdentities] [P.RespectsIso]
  定义体: StructuredArrow.closedUnderColimitsOfShape_discrete_empty (L := 𝟭 _) P

Depends on / 依赖: Discrete, IsClosedUnderColimitsOfShape, PEmpty
-/
instance Under.closedUnderColimitsOfShape_discrete_empty [P.ContainsIdentities] [P.RespectsIso] :
    (P.underObj (X := X)).IsClosedUnderColimitsOfShape (Discrete PEmpty.{1}) :=
  StructuredArrow.closedUnderColimitsOfShape_discrete_empty (L := 𝟭 _) P

/--
Instance `Under.closedUnderColimitsOfShape_pushout` / 实例 `Under.closedUnderColimitsOfShape_pushout`

English:
instance Under.closedUnderColimitsOfShape_pushout
  signature: [HasPushouts T]
  body: by
  rw [ObjectProperty.isClosedUnderColimitsOfShape_iff_op]; rw [←
    ObjectProperty.isClosedUnderLimitsOfShape_inverseImage_iff _ _ (Over.opEquivOpUnder _)]; rw [MorphismProperty.inverseImage_op_underObj]; rw [ObjectProperty.isClosedUnderLimitsOfShape_iff_of_equivalence _ walkingSpanOpEquiv]
  infer_instance

中文:
实例 Under.closedUnderColimitsOfShape_pushout
  签名: [有Pushouts T]
  定义体: by
  rw [ObjectProperty.isClosedUnderColimitsOfShape_iff_op]; rw [←
    ObjectProperty.isClosedUnderLimitsOfShape_inverseImage_iff _ _ (Over.opEquivOpUnder _)]; rw [MorphismProperty.inverseImage_op_underObj]; rw [ObjectProperty.isClosedUnderLimitsOfShape_iff_of_equivalence _ walkingSpanOpEquiv]
  infer_instance

Depends on / 依赖: IsClosedUnderColimitsOfShape, MorphismProperty, MorphismProperty.inverseImage_op_underObj, ObjectProperty, ObjectProperty.isClosedUnderColimitsOfShape_iff_op, ObjectProperty.isClosedUnderLimitsOfShape_iff_of_equivalence, ObjectProperty.isClosedUnderLimitsOfShape_inverseImage_iff, Over.opEquivOpUnder, WalkingSpan, infer_instance, inverseImage_op_underObj, isClosedUnderColimitsOfShape_iff_op, isClosedUnderLimitsOfShape_iff_of_equivalence, isClosedUnderLimitsOfShape_inverseImage_iff, opEquivOpUnder, walkingSpanOpEquiv
-/
instance Under.closedUnderColimitsOfShape_pushout [HasPushouts T]
    [P.IsStableUnderComposition] [P.IsStableUnderCobaseChange] [P.HasOfPrecompProperty P] :
    (P.underObj (X := X)).IsClosedUnderColimitsOfShape WalkingSpan := by
  rw [ObjectProperty.isClosedUnderColimitsOfShape_iff_op]; rw [←
    ObjectProperty.isClosedUnderLimitsOfShape_inverseImage_iff _ _ (Over.opEquivOpUnder _)]; rw [MorphismProperty.inverseImage_op_underObj]; rw [ObjectProperty.isClosedUnderLimitsOfShape_iff_of_equivalence _ walkingSpanOpEquiv]
  infer_instance

end

namespace MorphismProperty.Over

variable (X : T)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.ContainsIdentities]
  signature: [P.RespectsIso]
  body: by
  apply +allowSynthFailures forgetCreatesLimitsOfShapeOfClosed
  · exact inferInstanceAs (HasLimitsOfShape _ (Over X))
  · apply Over.closedUnderLimitsOfShape_discrete_empty _

中文:
实例 [P.余ntainsIdentities]
  签名: [P.RespectsIso]
  定义体: by
  apply +allowSynthFailures forgetCreatesLimitsOfShapeOfClosed
  · exact inferInstanceAs (HasLimitsOfShape _ (Over X))
  · apply Over.closedUnderLimitsOfShape_discrete_empty _

Depends on / 依赖: HasLimitsOfShape, Over.closedUnderLimitsOfShape_discrete_empty, allowSynthFailures, closedUnderLimitsOfShape_discrete_empty, forgetCreatesLimitsOfShapeOfClosed
-/
noncomputable instance [P.ContainsIdentities] [P.RespectsIso] :
    CreatesLimitsOfShape (Discrete PEmpty.{1}) (Over.forget P ⊤ X) := by
  apply +allowSynthFailures forgetCreatesLimitsOfShapeOfClosed
  · exact inferInstanceAs (HasLimitsOfShape _ (Over X))
  · apply Over.closedUnderLimitsOfShape_discrete_empty _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {X} in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.ContainsIdentities]
  signature: (Y : P.Over ⊤ X)
  body: Over.homMk Y.hom
  uniq a := by
    ext
    · simp only [mk_left, homMk_hom, Over.homMk_left]
      rw [← Over.w a]
      simp only [mk_left, Functor.const_obj_obj, mk_hom, Category.comp_id]

中文:
实例 [P.余ntainsIdentities]
  签名: (Y : P.Over ⊤ X)
  定义体: Over.homMk Y.hom
  uniq a := by
    ext
    · simp only [mk_left, homMk_hom, Over.homMk_left]
      rw [← Over.w a]
      simp only [mk_left, Functor.const_obj_obj, mk_hom, Category.comp_id]

Depends on / 依赖: Over.homMk, Y.hom
-/
instance [P.ContainsIdentities] (Y : P.Over ⊤ X) :
    Unique (Y ⟶ Over.mk ⊤ (𝟙 X) (P.id_mem X)) where
  default := Over.homMk Y.hom
  uniq a := by
    ext
    · simp only [mk_left, homMk_hom, Over.homMk_left]
      rw [← Over.w a]
      simp only [mk_left, Functor.const_obj_obj, mk_hom, Category.comp_id]

/--
Definition of `mkIdTerminal` / `mkIdTerminal` 的定义

English:
definition mkIdTerminal
  signature: [P.ContainsIdentities]
  body: IsTerminal.ofUnique _

中文:
定义 mkIdTerminal
  签名: [P.余ntainsIdentities]
  定义体: IsTerminal.ofUnique _

Depends on / 依赖: IsTerminal, IsTerminal.ofUnique, ofUnique
-/
def mkIdTerminal [P.ContainsIdentities] :
    IsTerminal (Over.mk ⊤ (𝟙 X) (P.id_mem X)) :=
  IsTerminal.ofUnique _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.ContainsIdentities]
  signature: : HasTerminal (P.Over ⊤ X)
  body: let h : IsTerminal (Over.mk ⊤ (𝟙 X) (P.id_mem X)) := Over.mkIdTerminal P X
  h.hasTerminal

中文:
实例 [P.余ntainsIdentities]
  签名: : 有终止 (P.Over ⊤ X)
  定义体: let h : IsTerminal (Over.mk ⊤ (𝟙 X) (P.id_mem X)) := Over.mkIdTerminal P X
  h.hasTerminal

Depends on / 依赖: IsTerminal, Over.mk, Over.mkIdTerminal, P.id_mem, h.hasTerminal, hasTerminal, id_mem, mkIdTerminal
-/
instance [P.ContainsIdentities] : HasTerminal (P.Over ⊤ X) :=
  let h : IsTerminal (Over.mk ⊤ (𝟙 X) (P.id_mem X)) := Over.mkIdTerminal P X
  h.hasTerminal

/--
Instance `createsLimitsOfShape_walkingCospan` / 实例 `createsLimitsOfShape_walkingCospan`

English:
instance createsLimitsOfShape_walkingCospan
  signature: [HasPullbacks T]
  body: CostructuredArrow.createsLimitsOfShape_walkingCospan _ _

中文:
实例 createsLimitsOfShape_walkingCospan
  签名: [有Pullbacks T]
  定义体: CostructuredArrow.createsLimitsOfShape_walkingCospan _ _

Depends on / 依赖: CostructuredArrow, CostructuredArrow.createsLimitsOfShape_walkingCospan, createsLimitsOfShape_walkingCospan
-/
noncomputable instance createsLimitsOfShape_walkingCospan [HasPullbacks T]
    [P.IsStableUnderComposition] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    CreatesLimitsOfShape WalkingCospan (Over.forget P ⊤ X) :=
  CostructuredArrow.createsLimitsOfShape_walkingCospan _ _

/-- If `P` is stable under composition, base change and satisfies post-cancellation,
`P.Over ⊤ X` has pullbacks -/
instance (priority := 900) hasPullbacks [HasPullbacks T] [P.IsStableUnderComposition]
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] : HasPullbacks (P.Over ⊤ X) :=
  CostructuredArrow.hasPullbacks _ _

variable [HasPullbacks T] [P.IsMultiplicative]
  [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]

/--
Instance `hasFiniteLimits` / 实例 `hasFiniteLimits`

English:
instance hasFiniteLimits
  signature: : HasFiniteLimits (P.Over ⊤ X)
  body: hasFiniteLimits_of_hasTerminal_and_pullbacks

中文:
实例 hasFiniteLimits
  签名: : 有有限极限 (P.Over ⊤ X)
  定义体: hasFiniteLimits_of_hasTerminal_and_pullbacks

Depends on / 依赖: hasFiniteLimits_of_hasTerminal_and_pullbacks
-/
instance hasFiniteLimits : HasFiniteLimits (P.Over ⊤ X) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CreatesFiniteLimits (Over.forget P ⊤ X)
  body: createsFiniteLimitsOfCreatesTerminalAndPullbacks _

中文:
实例 :
  签名: 创造有限极限 (Over.forget P ⊤ X)
  定义体: createsFiniteLimitsOfCreatesTerminalAndPullbacks _

Depends on / 依赖: createsFiniteLimitsOfCreatesTerminalAndPullbacks
-/
noncomputable instance : CreatesFiniteLimits (Over.forget P ⊤ X) :=
  createsFiniteLimitsOfCreatesTerminalAndPullbacks _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteWidePullbacks
  signature: T] : HasFiniteLimits (P.Over ⊤ X)
  body: hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits (Over.forget P ⊤ X)

中文:
实例 [有FiniteWidePullbacks
  签名: T] : 有有限极限 (P.Over ⊤ X)
  定义体: hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits (Over.forget P ⊤ X)

Depends on / 依赖: Over.forget, forget, hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits
-/
instance [HasFiniteWidePullbacks T] : HasFiniteLimits (P.Over ⊤ X) :=
  hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits (Over.forget P ⊤ X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteLimits (Over.forget P ⊤ X)
  body: preservesFiniteLimits_of_preservesTerminal_and_pullbacks (Over.forget P ⊤ X)

中文:
实例 :
  签名: 保持FiniteLimits (Over.forget P ⊤ X)
  定义体: preservesFiniteLimits_of_preservesTerminal_and_pullbacks (Over.forget P ⊤ X)

Depends on / 依赖: Over.forget, forget, preservesFiniteLimits_of_preservesTerminal_and_pullbacks
-/
instance : PreservesFiniteLimits (Over.forget P ⊤ X) :=
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks (Over.forget P ⊤ X)

instance {X Y : T} (f : X ⟶ Y) : PreservesFiniteLimits (pullback P ⊤ f) where
  preservesFiniteLimits J _ _ := by
    have : PreservesLimitsOfShape J
        (MorphismProperty.Over.pullback P ⊤ f ⋙ MorphismProperty.Over.forget _ _ _) :=
inferInstanceAs PreservesLimitsOfShape J
        Over.forget _ _ _ ⋙ CategoryTheory.Over.pullback f
    exact preservesLimitsOfShape_of_reflects_of_preserves
      (MorphismProperty.Over.pullback P ⊤ f) (MorphismProperty.Over.forget _ _ _)

end MorphismProperty.Over

namespace MorphismProperty.Under

variable (X : T)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.ContainsIdentities]
  signature: [P.RespectsIso]
  body: by
  apply +allowSynthFailures forgetCreatesColimitsOfShapeOfClosed
  · exact inferInstanceAs (HasColimitsOfShape _ (Under X))
  · apply Under.closedUnderColimitsOfShape_discrete_empty _

中文:
实例 [P.余ntainsIdentities]
  签名: [P.RespectsIso]
  定义体: by
  apply +allowSynthFailures forgetCreatesColimitsOfShapeOfClosed
  · exact inferInstanceAs (HasColimitsOfShape _ (Under X))
  · apply Under.closedUnderColimitsOfShape_discrete_empty _

Depends on / 依赖: HasColimitsOfShape, Under.closedUnderColimitsOfShape_discrete_empty, allowSynthFailures, closedUnderColimitsOfShape_discrete_empty, forgetCreatesColimitsOfShapeOfClosed
-/
noncomputable instance [P.ContainsIdentities] [P.RespectsIso] :
    CreatesColimitsOfShape (Discrete PEmpty.{1}) (Under.forget P ⊤ X) := by
  apply +allowSynthFailures forgetCreatesColimitsOfShapeOfClosed
  · exact inferInstanceAs (HasColimitsOfShape _ (Under X))
  · apply Under.closedUnderColimitsOfShape_discrete_empty _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {X} in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.ContainsIdentities]
  signature: (Y : P.Under ⊤ X)
  body: Under.homMk Y.hom (by simp)
  uniq a := by ext; simp [← Under.w a]

中文:
实例 [P.余ntainsIdentities]
  签名: (Y : P.Under ⊤ X)
  定义体: Under.homMk Y.hom (by simp)
  uniq a := by ext; simp [← Under.w a]

Depends on / 依赖: Under.homMk, Y.hom
-/
instance [P.ContainsIdentities] (Y : P.Under ⊤ X) :
    Unique (Under.mk ⊤ (𝟙 X) (P.id_mem X) ⟶ Y) where
  default := Under.homMk Y.hom (by simp)
  uniq a := by ext; simp [← Under.w a]

/--
Definition of `mkIdInitial` / `mkIdInitial` 的定义

English:
definition mkIdInitial
  signature: [P.ContainsIdentities]
  body: .ofUnique _

中文:
定义 mkIdInitial
  签名: [P.余ntainsIdentities]
  定义体: .ofUnique _

Depends on / 依赖: ofUnique
-/
def mkIdInitial [P.ContainsIdentities] :
    IsInitial (Under.mk ⊤ (𝟙 X) (P.id_mem X)) :=
  .ofUnique _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.ContainsIdentities]
  signature: : HasInitial (P.Under ⊤ X)
  body: (Under.mkIdInitial P X).hasInitial

中文:
实例 [P.余ntainsIdentities]
  签名: : HasInitial (P.Under ⊤ X)
  定义体: (Under.mkIdInitial P X).hasInitial

Depends on / 依赖: Under.mkIdInitial, hasInitial, mkIdInitial
-/
instance [P.ContainsIdentities] : HasInitial (P.Under ⊤ X) :=
  (Under.mkIdInitial P X).hasInitial

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasPushouts
  signature: T]
  body: by
  apply +allowSynthFailures forgetCreatesColimitsOfShapeOfClosed
  · exact inferInstanceAs (HasColimitsOfShape WalkingSpan (Under X))
  · apply Under.closedUnderColimitsOfShape_pushout

中文:
实例 [有Pushouts
  签名: T]
  定义体: by
  apply +allowSynthFailures forgetCreatesColimitsOfShapeOfClosed
  · exact inferInstanceAs (HasColimitsOfShape WalkingSpan (Under X))
  · apply Under.closedUnderColimitsOfShape_pushout

Depends on / 依赖: HasColimitsOfShape, Under.closedUnderColimitsOfShape_pushout, WalkingSpan, allowSynthFailures, closedUnderColimitsOfShape_pushout, forgetCreatesColimitsOfShapeOfClosed
-/
noncomputable instance [HasPushouts T]
    [P.IsStableUnderComposition] [P.IsStableUnderCobaseChange] [P.HasOfPrecompProperty P] :
    CreatesColimitsOfShape WalkingSpan (Under.forget P ⊤ X) := by
  apply +allowSynthFailures forgetCreatesColimitsOfShapeOfClosed
  · exact inferInstanceAs (HasColimitsOfShape WalkingSpan (Under X))
  · apply Under.closedUnderColimitsOfShape_pushout

/-- If `P` is stable under composition, cobase change and satisfies pre-cancellation,
`P.Under ⊤ X` has pushouts. -/
instance (priority := 900) [HasPushouts T] [P.IsStableUnderComposition]
    [P.IsStableUnderCobaseChange] [P.HasOfPrecompProperty P] : HasPushouts (P.Under ⊤ X) := by
  apply +allowSynthFailures hasColimitsOfShape_of_closedUnderColimitsOfShape
  · exact inferInstanceAs (HasColimitsOfShape WalkingSpan (Under X))
  · apply Under.closedUnderColimitsOfShape_pushout

variable [HasPushouts T] [P.IsStableUnderComposition] [P.ContainsIdentities]
  [P.IsStableUnderCobaseChange] [P.HasOfPrecompProperty P]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CreatesFiniteColimits (Under.forget P ⊤ X)
  body: createsFiniteColimitsOfCreatesInitialAndPushouts _

中文:
实例 :
  签名: 创造有限余极限 (Under.forget P ⊤ X)
  定义体: createsFiniteColimitsOfCreatesInitialAndPushouts _

Depends on / 依赖: createsFiniteColimitsOfCreatesInitialAndPushouts
-/
noncomputable instance : CreatesFiniteColimits (Under.forget P ⊤ X) :=
  createsFiniteColimitsOfCreatesInitialAndPushouts _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteWidePushouts
  signature: T] : HasFiniteColimits (P.Under ⊤ X)
  body: hasFiniteColimits_of_hasColimits_of_createsFiniteColimits (Under.forget P ⊤ X)

中文:
实例 [有FiniteWidePushouts
  签名: T] : 有有限余极限 (P.Under ⊤ X)
  定义体: hasFiniteColimits_of_hasColimits_of_createsFiniteColimits (Under.forget P ⊤ X)

Depends on / 依赖: Under.forget, forget, hasFiniteColimits_of_hasColimits_of_createsFiniteColimits
-/
instance [HasFiniteWidePushouts T] : HasFiniteColimits (P.Under ⊤ X) :=
  hasFiniteColimits_of_hasColimits_of_createsFiniteColimits (Under.forget P ⊤ X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteColimits (Under.forget P ⊤ X)
  body: preservesFiniteColimits_of_preservesInitial_and_pushouts (Under.forget P ⊤ X)

中文:
实例 :
  签名: 保持FiniteColimits (Under.forget P ⊤ X)
  定义体: preservesFiniteColimits_of_preservesInitial_and_pushouts (Under.forget P ⊤ X)

Depends on / 依赖: Under.forget, forget, preservesFiniteColimits_of_preservesInitial_and_pushouts
-/
instance : PreservesFiniteColimits (Under.forget P ⊤ X) :=
  preservesFiniteColimits_of_preservesInitial_and_pushouts (Under.forget P ⊤ X)

end MorphismProperty.Under

end CategoryTheory
