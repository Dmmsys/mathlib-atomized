/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Limits.ConeCategory
public import Mathlib.CategoryTheory.Limits.Constructions.WeaklyInitial
public import Mathlib.CategoryTheory.Subobject.Comma

/-!
# Adjoint functor theorem

This file proves the (general) adjoint functor theorem, in the form:
* If `G : D ⥤ C` preserves limits and `D` has limits, and satisfies the solution set condition,
  then it has a left adjoint: `isRightAdjoint_of_preservesLimits_of_solutionSetCondition`.

We show that the converse holds, i.e. that if `G` has a left adjoint then it satisfies the solution
set condition, see `solutionSetCondition_of_isRightAdjoint`
(the file `CategoryTheory/Adjunction/Limits` already shows it preserves limits).

We define the *solution set condition* for the functor `G : D ⥤ C` to mean, for every object
`A : C`, there is a set-indexed family ${f_i : A ⟶ G (B_i)}$ such that any morphism `A ⟶ G X`
factors through one of the `f_i`.

This file also proves the special adjoint functor theorem, in the form:
* If `G : D ⥤ C` preserves limits and `D` is complete, well-powered and has a small coseparating
  set, then `G` has a left adjoint: `isRightAdjoint_of_preservesLimits_of_isCoseparating`

Finally, we prove the following corollaries of the special adjoint functor theorem:
* If `C` is complete, well-powered and has a small coseparating set, then it is cocomplete:
  `hasColimits_of_hasLimits_of_isCoseparating`, `hasColimits_of_hasLimits_of_hasCoseparator`
* If `C` is cocomplete, co-well-powered and has a small separating set, then it is complete:
  `hasLimits_of_hasColimits_of_isSeparating`, `hasLimits_of_hasColimits_of_hasSeparator`

-/

@[expose] public section


universe w v v₁ u u₁ u'

namespace CategoryTheory

open Limits

variable {J : Type v}
variable {C : Type u} [Category.{v} C]

/--
Definition of `SolutionSetCondition` / `SolutionSetCondition` 的定义

English:
definition SolutionSetCondition
  signature: {D : Type u₁} [Category.{v₁} D] (G : D ⥤ C)
  body: forall A : C,
    exists (ι : Type w) (B : ι -> D) (f : forall i : ι, A ⟶ G.obj (B i)),
      forall (X) (h : A ⟶ G.obj X), exists (i : ι) (g : B i ⟶ X), f i ≫ G.map g = h

中文:
定义 SolutionSetCondition
  签名: {D : 类型u₁} [Category.{v₁} D] (G : D ⥤ C)
  定义体: forall A : C,
    exists (ι : Type w) (B : ι -> D) (f : forall i : ι, A ⟶ G.obj (B i)),
      forall (X) (h : A ⟶ G.obj X), exists (i : ι) (g : B i ⟶ X), f i ≫ G.map g = h

Depends on / 依赖: G.map, G.obj
-/
def SolutionSetCondition {D : Type u₁} [Category.{v₁} D] (G : D ⥤ C) : Prop :=
  forall A : C,
    exists (ι : Type w) (B : ι -> D) (f : forall i : ι, A ⟶ G.obj (B i)),
      forall (X) (h : A ⟶ G.obj X), exists (i : ι) (g : B i ⟶ X), f i ≫ G.map g = h

section GeneralAdjointFunctorTheorem

variable {D : Type u₁} [Category.{v₁} D]
variable (G : D ⥤ C)

/--
theorem `solutionSetCondition_of_isRightAdjoint` / 定理 `solutionSetCondition_of_isRightAdjoint`

English:
theorem solutionSetCondition_of_isRightAdjoint
  given: [G.IsRightAdjoint]
  statement: SolutionSetCondition.{w} G
  proof: by
  intro A
  refine
    ⟨PUnit, fun _ => G.leftAdjoint.obj A, fun _ => (Adjunction.ofIsRightAdjoint G).unit.app A, ?_⟩
  intro B h
  refine ⟨PUnit.unit, ((Adjunction.ofIsRightAdjoint G).homEquiv _ _).symm h, ?_⟩
  rw [← Adjunction.homEquiv_unit]; rw [Equiv.apply_symm_apply]

中文:
定理 solutionSetCondition_of_isRightAdjoint
  条件: [G.IsRightAdjoint]
  结论: SolutionSetCondition.{w} G
  证明: by
  intro A
  refine
    ⟨PUnit, fun _ => G.leftAdjoint.obj A, fun _ => (Adjunction.ofIsRightAdjoint G).unit.app A, ?_⟩
  intro B h
  refine ⟨PUnit.unit, ((Adjunction.ofIsRightAdjoint G).homEquiv _ _).symm h, ?_⟩
  rw [← Adjunction.homEquiv_unit]; rw [Equiv.apply_symm_apply]

Depends on / 依赖: Adjunction, Adjunction.homEquiv_unit, Adjunction.ofIsRightAdjoint, Equiv.apply_symm_apply, G.leftAdjoint.obj, PUnit.unit, apply_symm_apply, homEquiv, homEquiv_unit, leftAdjoint, ofIsRightAdjoint, unit.app
-/
theorem solutionSetCondition_of_isRightAdjoint [G.IsRightAdjoint] : SolutionSetCondition.{w} G := by
  intro A
  refine
    ⟨PUnit, fun _ => G.leftAdjoint.obj A, fun _ => (Adjunction.ofIsRightAdjoint G).unit.app A, ?_⟩
  intro B h
  refine ⟨PUnit.unit, ((Adjunction.ofIsRightAdjoint G).homEquiv _ _).symm h, ?_⟩
  rw [← Adjunction.homEquiv_unit]; rw [Equiv.apply_symm_apply]

/--
lemma `isRightAdjoint_of_preservesLimits_of_solutionSetCondition` / 引理 `isRightAdjoint_of_preservesLimits_of_solutionSetCondition`

English:
lemma isRightAdjoint_of_preservesLimits_of_solutionSetCondition
  statement: [HasLimits D]
  proof: by
  refine @isRightAdjointOfStructuredArrowInitials _ _ _ _ G ?_
  intro A
  specialize hG A
  choose ι B f g using hG
  let B' : ι -> StructuredArrow A G := fun i => StructuredArrow.mk (f i)
  have hB' : forall A' : StructuredArrow A G, exists i, Nonempty (B' i ⟶ A') := by
    intro A'
    obtain 

中文:
引理 isRightAdjoint_of_preservesLimits_of_solutionSetCondition
  结论: [HasLimits D]
  证明: by
  refine @isRightAdjointOfStructuredArrowInitials _ _ _ _ G ?_
  intro A
  specialize hG A
  choose ι B f g using hG
  let B' : ι -> StructuredArrow A G := fun i => StructuredArrow.mk (f i)
  have hB' : forall A' : StructuredArrow A G, exists i, Nonempty (B' i ⟶ A') := by
    intro A'
    obtain 

Depends on / 依赖: Nonempty, StructuredArrow, StructuredArrow.homMk, StructuredArrow.mk, hasInitial_of_weakly_initial_and_hasWideEqualizers, has_weakly_initial_of_weakly_initial_set_and_hasProducts, isRightAdjointOfStructuredArrowInitials, specialize
-/
lemma isRightAdjoint_of_preservesLimits_of_solutionSetCondition [HasLimits D]
    [PreservesLimitsOfSize.{v₁, v₁} G] (hG : SolutionSetCondition.{v₁} G) : G.IsRightAdjoint := by
  refine @isRightAdjointOfStructuredArrowInitials _ _ _ _ G ?_
  intro A
  specialize hG A
  choose ι B f g using hG
  let B' : ι -> StructuredArrow A G := fun i => StructuredArrow.mk (f i)
  have hB' : forall A' : StructuredArrow A G, exists i, Nonempty (B' i ⟶ A') := by
    intro A'
    obtain ⟨i, _, t⟩ := g _ A'.hom
    exact ⟨i, ⟨StructuredArrow.homMk _ t⟩⟩
  obtain ⟨T, hT⟩ := has_weakly_initial_of_weakly_initial_set_and_hasProducts hB'
  apply hasInitial_of_weakly_initial_and_hasWideEqualizers hT

end GeneralAdjointFunctorTheorem

section SpecialAdjointFunctorTheorem

variable {D : Type u'} [Category.{v} D]

/--
lemma `isRightAdjoint_of_preservesLimits_of_isCoseparating` / 引理 `isRightAdjoint_of_preservesLimits_of_isCoseparating`

English:
lemma isRightAdjoint_of_preservesLimits_of_isCoseparating
  statement: [HasLimits D] [WellPowered.{v} D]
  proof: by
  have : forall A, HasInitial (StructuredArrow A G) := fun A =>
    hasInitial_of_isCoseparating.{v} (StructuredArrow.isCoseparating_inverseImage_proj A G hP)
  exact isRightAdjointOfStructuredArrowInitials _

中文:
引理 isRightAdjoint_of_preservesLimits_of_isCoseparating
  结论: [HasLimits D] [WellPowered.{v} D]
  证明: by
  have : forall A, HasInitial (StructuredArrow A G) := fun A =>
    hasInitial_of_isCoseparating.{v} (StructuredArrow.isCoseparating_inverseImage_proj A G hP)
  exact isRightAdjointOfStructuredArrowInitials _

Depends on / 依赖: HasInitial, StructuredArrow, StructuredArrow.isCoseparating_inverseImage_proj, hasInitial_of_isCoseparating, isCoseparating_inverseImage_proj, isRightAdjointOfStructuredArrowInitials
-/
lemma isRightAdjoint_of_preservesLimits_of_isCoseparating [HasLimits D] [WellPowered.{v} D]
    {P : ObjectProperty D} [ObjectProperty.Small.{v} P]
    (hP : P.IsCoseparating) (G : D ⥤ C) [PreservesLimits G] :
    G.IsRightAdjoint := by
  have : forall A, HasInitial (StructuredArrow A G) := fun A =>
    hasInitial_of_isCoseparating.{v} (StructuredArrow.isCoseparating_inverseImage_proj A G hP)
  exact isRightAdjointOfStructuredArrowInitials _

/--
lemma `isLeftAdjoint_of_preservesColimits_of_isSeparating` / 引理 `isLeftAdjoint_of_preservesColimits_of_isSeparating`

English:
lemma isLeftAdjoint_of_preservesColimits_of_isSeparating
  statement: [HasColimits C] [WellPowered.{v} Cᵒᵖ]
  proof: have : forall A, HasTerminal (CostructuredArrow F A) := fun A =>
    hasTerminal_of_isSeparating.{v} (CostructuredArrow.isSeparating_inverseImage_proj F A h𝒢)
  isLeftAdjoint_of_costructuredArrowTerminals _

中文:
引理 isLeftAdjoint_of_preservesColimits_of_isSeparating
  结论: [HasColimits C] [WellPowered.{v} Cᵒᵖ]
  证明: have : forall A, HasTerminal (CostructuredArrow F A) := fun A =>
    hasTerminal_of_isSeparating.{v} (CostructuredArrow.isSeparating_inverseImage_proj F A h𝒢)
  isLeftAdjoint_of_costructuredArrowTerminals _

Depends on / 依赖: CostructuredArrow, CostructuredArrow.isSeparating_inverseImage_proj, HasTerminal, hasTerminal_of_isSeparating, isLeftAdjoint_of_costructuredArrowTerminals, isSeparating_inverseImage_proj
-/
lemma isLeftAdjoint_of_preservesColimits_of_isSeparating [HasColimits C] [WellPowered.{v} Cᵒᵖ]
    {P : ObjectProperty C} [ObjectProperty.Small.{v} P]
    (h𝒢 : P.IsSeparating) (F : C ⥤ D) [PreservesColimits F] :
    F.IsLeftAdjoint :=
  have : forall A, HasTerminal (CostructuredArrow F A) := fun A =>
    hasTerminal_of_isSeparating.{v} (CostructuredArrow.isSeparating_inverseImage_proj F A h𝒢)
  isLeftAdjoint_of_costructuredArrowTerminals _

end SpecialAdjointFunctorTheorem

namespace Limits

/--
theorem `hasColimits_of_hasLimits_of_isCoseparating` / 定理 `hasColimits_of_hasLimits_of_isCoseparating`

English:
theorem hasColimits_of_hasLimits_of_isCoseparating
  statement: [HasLimits C] [WellPowered.{v} C]
  proof: { has_colimits_of_shape := fun _ _ =>
      hasColimitsOfShape_iff_isRightAdjoint_const.2
        (isRightAdjoint_of_preservesLimits_of_isCoseparating hP _) }

中文:
定理 hasColimits_of_hasLimits_of_isCoseparating
  结论: [HasLimits C] [WellPowered.{v} C]
  证明: { has_colimits_of_shape := fun _ _ =>
      hasColimitsOfShape_iff_isRightAdjoint_const.2
        (isRightAdjoint_of_preservesLimits_of_isCoseparating hP _) }

Depends on / 依赖: hasColimitsOfShape_iff_isRightAdjoint_const, has_colimits_of_shape, isRightAdjoint_of_preservesLimits_of_isCoseparating
-/
theorem hasColimits_of_hasLimits_of_isCoseparating [HasLimits C] [WellPowered.{v} C]
    {P : ObjectProperty C} [ObjectProperty.Small.{v} P] (hP : P.IsCoseparating) : HasColimits C :=
  { has_colimits_of_shape := fun _ _ =>
      hasColimitsOfShape_iff_isRightAdjoint_const.2
        (isRightAdjoint_of_preservesLimits_of_isCoseparating hP _) }

/--
theorem `hasLimits_of_hasColimits_of_isSeparating` / 定理 `hasLimits_of_hasColimits_of_isSeparating`

English:
theorem hasLimits_of_hasColimits_of_isSeparating
  statement: [HasColimits C] [WellPowered.{v} Cᵒᵖ]
  proof: { has_limits_of_shape := fun _ _ =>
      hasLimitsOfShape_iff_isLeftAdjoint_const.2
        (isLeftAdjoint_of_preservesColimits_of_isSeparating hP _) }

中文:
定理 hasLimits_of_hasColimits_of_isSeparating
  结论: [HasColimits C] [WellPowered.{v} Cᵒᵖ]
  证明: { has_limits_of_shape := fun _ _ =>
      hasLimitsOfShape_iff_isLeftAdjoint_const.2
        (isLeftAdjoint_of_preservesColimits_of_isSeparating hP _) }

Depends on / 依赖: hasLimitsOfShape_iff_isLeftAdjoint_const, has_limits_of_shape, isLeftAdjoint_of_preservesColimits_of_isSeparating
-/
theorem hasLimits_of_hasColimits_of_isSeparating [HasColimits C] [WellPowered.{v} Cᵒᵖ]
    {P : ObjectProperty C} [ObjectProperty.Small.{v} P] (hP : P.IsSeparating) : HasLimits C :=
  { has_limits_of_shape := fun _ _ =>
      hasLimitsOfShape_iff_isLeftAdjoint_const.2
        (isLeftAdjoint_of_preservesColimits_of_isSeparating hP _) }

/--
theorem `hasLimits_of_hasColimits_of_hasSeparator` / 定理 `hasLimits_of_hasColimits_of_hasSeparator`

English:
theorem hasLimits_of_hasColimits_of_hasSeparator
  statement: [HasColimits C] [HasSeparator C]
  proof: hasLimits_of_hasColimits_of_isSeparating isSeparator_separator C

中文:
定理 hasLimits_of_hasColimits_of_hasSeparator
  结论: [HasColimits C] [HasSeparator C]
  证明: hasLimits_of_hasColimits_of_isSeparating isSeparator_separator C

Depends on / 依赖: hasLimits_of_hasColimits_of_isSeparating, isSeparator_separator
-/
theorem hasLimits_of_hasColimits_of_hasSeparator [HasColimits C] [HasSeparator C]
    [WellPowered.{v} Cᵒᵖ] : HasLimits C :=
hasLimits_of_hasColimits_of_isSeparating isSeparator_separator C

/--
theorem `hasColimits_of_hasLimits_of_hasCoseparator` / 定理 `hasColimits_of_hasLimits_of_hasCoseparator`

English:
theorem hasColimits_of_hasLimits_of_hasCoseparator
  statement: [HasLimits C] [HasCoseparator C]
  proof: hasColimits_of_hasLimits_of_isCoseparating isCoseparator_coseparator C

中文:
定理 hasColimits_of_hasLimits_of_hasCoseparator
  结论: [HasLimits C] [HasCoseparator C]
  证明: hasColimits_of_hasLimits_of_isCoseparating isCoseparator_coseparator C

Depends on / 依赖: hasColimits_of_hasLimits_of_isCoseparating, isCoseparator_coseparator
-/
theorem hasColimits_of_hasLimits_of_hasCoseparator [HasLimits C] [HasCoseparator C]
    [WellPowered.{v} C] : HasColimits C :=
hasColimits_of_hasLimits_of_isCoseparating isCoseparator_coseparator C

end Limits

end CategoryTheory
