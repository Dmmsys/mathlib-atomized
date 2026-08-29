/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.SmallObject.Construction
public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
public import Mathlib.CategoryTheory.MorphismProperty.IsSmall
public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# Cardinals that are suitable for the small object argument

In this file, given a class of morphisms `I : MorphismProperty C` and
a regular cardinal `κ : Cardinal.{w}`, we define a typeclass
`IsCardinalForSmallObjectArgument I κ` which requires certain
smallness properties (`I` is `w`-small, `C` is locally `w`-small),
the existence of certain colimits (pushouts, coproducts of size `w`,
and the condition `HasIterationOfShape κ.ord.ToType C` about the
existence of colimits indexed by limit ordinal smaller than or equal
to `κ.ord`), and the technical assumption that if `A` is the
a morphism in `I`, then the functor `Hom(A, _)` should commute
with the filtering colimits corresponding to relative
`I`-cell complexes. (This last condition shall hold when `κ`
is the successor of an infinite cardinal `c` such that all these objects `A` are `c`-presentable,
see `Mathlib/CategoryTheory/Presentable/Basic.lean`.)

Given `I : MorphismProperty C`, we shall say that `I` permits
the small object argument if there exists `κ` such that
`IsCardinalForSmallObjectArgument I κ` holds. See the file
`Mathlib/CategoryTheory/SmallObject/Basic.lean` for the definition of this typeclass
`HasSmallObjectArgument` and an outline of the proof.

## Main results

Assuming `IsCardinalForSmallObjectArgument I κ`, any morphism `f : X ⟶ Y`
is factored as `ιObj I κ f ≫ πObj I κ f = f`. It is shown that `ιObj I κ f`
is a relative `I`-cell complex (see `SmallObject.relativeCellComplexιObj`)
and that `πObj I κ f` has the right lifting property with respect to `I`
(see `SmallObject.rlp_πObj`). This construction is obtained by
iterating to the power `κ.ord.ToType` the functor `Arrow C ⥤ Arrow C` defined
in the file `Mathlib/CategoryTheory/SmallObject/Construction.lean`.
This factorization is functorial in `f`
and gives the property `HasFunctorialFactorization I.rlp.llp I.rlp`.
Finally, the lemma `llp_rlp_of_isCardinalForSmallObjectArgument`
(and its primed version) shows that the morphisms in `I.rlp.llp` are exactly
the retracts of the transfinite compositions (of shape `κ.ord.ToType`) of
pushouts of coproducts of morphisms in `I`.

## References
- https://ncatlab.org/nlab/show/small+object+argument

-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

open Category HomotopicalAlgebra Limits SmallObject

variable {C : Type u} [Category.{v} C] (I : MorphismProperty C)

namespace MorphismProperty

/--
Definition of `IsCardinalForSmallObjectArgument` / `IsCardinalForSmallObjectArgument` 的定义

English:
class IsCardinalForSmallObjectArgument
  parameters: (κ : Cardinal.{w}) [Fact κ.IsRegular]
  axioms and operations (6):
    - isSmall : IsSmall.{w} I  [default: by infer_instance]
    - locallySmall : LocallySmall.{w} C  [default: by infer_instance]
    - hasPushouts : HasPushouts C  [default: by infer_instance]
    - hasCoproducts : HasCoproducts.{w} C  [default: by infer_instance]
    - hasIterationOfShape : HasIterationOfShape κ.ord.ToType C  [default: by infer_instance]
    - preservesColimit({A B X Y : C} (i : A ⟶ B) (_ : I i) (f : X ⟶ Y) (hf : RelativeCellComplex.{w} (fun (_ : κ.ord.ToType) => I.homFamily) f)) : PreservesColimit hf.F (coyoneda.obj (Opposite.op A))

中文:
类 是CardinalForSmallObjectArgument
  参数: (κ : 基数.{w}) [Fact κ.是正则]
  公理与运算 (6 个):
    - isSmall : 是Small.{w} I  [默认: by infer_instance]
    - locallySmall : LocallySmall.{w} C  [默认: by infer_instance]
    - hasPushouts : 有Pushouts C  [默认: by infer_instance]
    - hasCoproducts : HasCoproducts.{w} C  [默认: by infer_instance]
    - hasIterationOfShape : 有IterationOfShape κ.ord.ToType C  [默认: by infer_instance]
    - preservesColimit({A B X Y : C} (i : A ⟶ B) (_ : I i) (f : X ⟶ Y) (hf : RelativeCellComplex.{w} (fun (_ : κ.ord.ToType) => I.homFamily) f)) : 保持余极限 hf.F (coyoneda.obj (对偶.op A))

Depends on / 依赖: HasCoproducts, HasIterationOfShape, HasPushouts, I.homFamily, LocallySmall, Opposite, Opposite.op, PreservesColimit, RelativeCellComplex, ToType, coyoneda, coyoneda.obj, hasCoproducts, hasIterationOfShape, hasPushouts, hf.F, homFamily, infer_instance, locallySmall, ord.ToType
-/
class IsCardinalForSmallObjectArgument (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [OrderBot κ.ord.ToType] : Prop where
  isSmall : IsSmall.{w} I := by infer_instance
  locallySmall : LocallySmall.{w} C := by infer_instance
  hasPushouts : HasPushouts C := by infer_instance
  hasCoproducts : HasCoproducts.{w} C := by infer_instance
  hasIterationOfShape : HasIterationOfShape κ.ord.ToType C := by infer_instance
  preservesColimit {A B X Y : C} (i : A ⟶ B) (_ : I i) (f : X ⟶ Y)
    (hf : RelativeCellComplex.{w} (fun (_ : κ.ord.ToType) => I.homFamily) f) :
    PreservesColimit hf.F (coyoneda.obj (Opposite.op A))

end MorphismProperty

namespace SmallObject

open MorphismProperty

variable (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [I.IsCardinalForSmallObjectArgument κ]

include I κ

/--
lemma `isSmall` / 引理 `isSmall`

English:
lemma isSmall
  statement: IsSmall.{w} I
  proof: IsCardinalForSmallObjectArgument.isSmall κ

中文:
引理 isSmall
  结论: 是Small.{w} I
  证明: IsCardinalForSmallObjectArgument.isSmall κ

Depends on / 依赖: IsCardinalForSmallObjectArgument, IsCardinalForSmallObjectArgument.isSmall, isSmall
-/
lemma isSmall : IsSmall.{w} I :=
  IsCardinalForSmallObjectArgument.isSmall κ

/--
lemma `locallySmall` / 引理 `locallySmall`

English:
lemma locallySmall
  statement: LocallySmall.{w} C
  proof: IsCardinalForSmallObjectArgument.locallySmall I κ

中文:
引理 locallySmall
  结论: LocallySmall.{w} C
  证明: IsCardinalForSmallObjectArgument.locallySmall I κ

Depends on / 依赖: IsCardinalForSmallObjectArgument, IsCardinalForSmallObjectArgument.locallySmall, locallySmall
-/
lemma locallySmall : LocallySmall.{w} C :=
  IsCardinalForSmallObjectArgument.locallySmall I κ

/--
lemma `hasIterationOfShape` / 引理 `hasIterationOfShape`

English:
lemma hasIterationOfShape
  statement: HasIterationOfShape κ.ord.ToType C
  proof: IsCardinalForSmallObjectArgument.hasIterationOfShape I

中文:
引理 hasIterationOfShape
  结论: 有IterationOfShape κ.ord.ToType C
  证明: IsCardinalForSmallObjectArgument.hasIterationOfShape I

Depends on / 依赖: IsCardinalForSmallObjectArgument, IsCardinalForSmallObjectArgument.hasIterationOfShape, hasIterationOfShape
-/
lemma hasIterationOfShape : HasIterationOfShape κ.ord.ToType C :=
  IsCardinalForSmallObjectArgument.hasIterationOfShape I

/--
lemma `hasPushouts` / 引理 `hasPushouts`

English:
lemma hasPushouts
  statement: HasPushouts C
  proof: IsCardinalForSmallObjectArgument.hasPushouts I κ

中文:
引理 hasPushouts
  结论: 有Pushouts C
  证明: IsCardinalForSmallObjectArgument.hasPushouts I κ

Depends on / 依赖: IsCardinalForSmallObjectArgument, IsCardinalForSmallObjectArgument.hasPushouts, hasPushouts
-/
lemma hasPushouts : HasPushouts C :=
  IsCardinalForSmallObjectArgument.hasPushouts I κ

/--
lemma `hasCoproducts` / 引理 `hasCoproducts`

English:
lemma hasCoproducts
  statement: HasCoproducts.{w} C
  proof: IsCardinalForSmallObjectArgument.hasCoproducts I κ

中文:
引理 hasCoproducts
  结论: HasCoproducts.{w} C
  证明: IsCardinalForSmallObjectArgument.hasCoproducts I κ

Depends on / 依赖: IsCardinalForSmallObjectArgument, IsCardinalForSmallObjectArgument.hasCoproducts, hasCoproducts
-/
lemma hasCoproducts : HasCoproducts.{w} C :=
  IsCardinalForSmallObjectArgument.hasCoproducts I κ

/--
lemma `preservesColimit` / 引理 `preservesColimit`

English:
lemma preservesColimit
  statement: {A B X Y : C} (i : A ⟶ B) (hi : I i) (f : X ⟶ Y)
  proof: IsCardinalForSmallObjectArgument.preservesColimit i hi f hf

中文:
引理 preservesColimit
  结论: {A B X Y : C} (i : A ⟶ B) (hi : I i) (f : X ⟶ Y)
  证明: IsCardinalForSmallObjectArgument.preservesColimit i hi f hf

Depends on / 依赖: IsCardinalForSmallObjectArgument, IsCardinalForSmallObjectArgument.preservesColimit, preservesColimit
-/
lemma preservesColimit {A B X Y : C} (i : A ⟶ B) (hi : I i) (f : X ⟶ Y)
    (hf : RelativeCellComplex.{w} (fun (_ : κ.ord.ToType) => I.homFamily) f) :
    PreservesColimit hf.F (coyoneda.obj (Opposite.op A)) :=
  IsCardinalForSmallObjectArgument.preservesColimit i hi f hf

/--
lemma `hasColimitsOfShape_discrete` / 引理 `hasColimitsOfShape_discrete`

English:
lemma hasColimitsOfShape_discrete
  given: (X Y : C) (p : X ⟶ Y)
  proof: by
  have := locallySmall I κ
  have := isSmall I κ
  have := hasCoproducts I κ
  exact hasColimitsOfShape_of_equivalence
    (Discrete.equivalence (equivShrink.{w} _)).symm

中文:
引理 hasColimitsOfShape_discrete
  条件: (X Y : C) (p : X ⟶ Y)
  证明: by
  have := locallySmall I κ
  have := isSmall I κ
  have := hasCoproducts I κ
  exact hasColimitsOfShape_of_equivalence
    (Discrete.equivalence (equivShrink.{w} _)).symm

Depends on / 依赖: Discrete, Discrete.equivalence, equivShrink, equivalence, hasColimitsOfShape_of_equivalence, hasCoproducts, isSmall, locallySmall
-/
lemma hasColimitsOfShape_discrete (X Y : C) (p : X ⟶ Y) :
    HasColimitsOfShape
      (Discrete (FunctorObjIndex I.homFamily p)) C := by
  have := locallySmall I κ
  have := isSmall I κ
  have := hasCoproducts I κ
  exact hasColimitsOfShape_of_equivalence
    (Discrete.equivalence (equivShrink.{w} _)).symm

/--
Definition of `succStruct` / `succStruct` 的定义

English:
definition succStruct
  signature: : SuccStruct (Arrow C ⥤ Arrow C)
  body: haveI := hasColimitsOfShape_discrete I κ
  haveI := hasPushouts I κ
  SuccStruct.ofNatTrans (ε I.homFamily)

中文:
定义 succStruct
  签名: : SuccStruct (箭头 C ⥤ 箭头 C)
  定义体: haveI := hasColimitsOfShape_discrete I κ
  haveI := hasPushouts I κ
  SuccStruct.ofNatTrans (ε I.homFamily)

Depends on / 依赖: I.homFamily, SuccStruct, SuccStruct.ofNatTrans, hasColimitsOfShape_discrete, hasPushouts, homFamily, ofNatTrans
-/
noncomputable def succStruct : SuccStruct (Arrow C ⥤ Arrow C) :=
  haveI := hasColimitsOfShape_discrete I κ
  haveI := hasPushouts I κ
  SuccStruct.ofNatTrans (ε I.homFamily)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `attachCellsOfSuccStructProp` / `attachCellsOfSuccStructProp` 的定义

English:
definition attachCellsOfSuccStructProp
  body: haveI := locallySmall I κ
  haveI := isSmall I κ
  haveI := hasColimitsOfShape_discrete I κ
  haveI := hasPushouts I κ
  AttachCells.ofArrowIso (attachCellsιFunctorObjOfSmall _ _)
    ((Functor.mapArrow ((evaluation _ _).obj f ⋙
      Arrow.leftFunc)).mapIso h.arrowIso.symm)

中文:
定义 attachCellsOfSuccStructProp
  定义体: haveI := locallySmall I κ
  haveI := isSmall I κ
  haveI := hasColimitsOfShape_discrete I κ
  haveI := hasPushouts I κ
  AttachCells.ofArrowIso (attachCellsιFunctorObjOfSmall _ _)
    ((Functor.mapArrow ((evaluation _ _).obj f ⋙
      Arrow.leftFunc)).mapIso h.arrowIso.symm)

Depends on / 依赖: Arrow.leftFunc, AttachCells, AttachCells.ofArrowIso, Functor, Functor.mapArrow, arrowIso, evaluation, h.arrowIso.symm, hasColimitsOfShape_discrete, hasPushouts, isSmall, leftFunc, locallySmall, mapArrow, mapIso, ofArrowIso
-/
noncomputable def attachCellsOfSuccStructProp
    {F G : Arrow C ⥤ Arrow C} {φ : F ⟶ G}
    (h : (succStruct I κ).prop φ) (f : Arrow C) :
    AttachCells.{w} I.homFamily (φ.app f).left :=
  haveI := locallySmall I κ
  haveI := isSmall I κ
  haveI := hasColimitsOfShape_discrete I κ
  haveI := hasPushouts I κ
  AttachCells.ofArrowIso (attachCellsιFunctorObjOfSmall _ _)
    ((Functor.mapArrow ((evaluation _ _).obj f ⋙
      Arrow.leftFunc)).mapIso h.arrowIso.symm)

/--
Definition of `propArrow` / `propArrow` 的定义

English:
definition propArrow
  signature: : MorphismProperty (Arrow C)
  body: fun _ _ f =>
  (coproducts.{w} I).pushouts f.left ∧ (isomorphisms C) f.right

中文:
定义 propArrow
  签名: : MorphismProperty (箭头 C)
  定义体: fun _ _ f =>
  (coproducts.{w} I).pushouts f.left ∧ (isomorphisms C) f.right
-/
def propArrow : MorphismProperty (Arrow C) := fun _ _ f =>
  (coproducts.{w} I).pushouts f.left ∧ (isomorphisms C) f.right

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `succStruct_prop_le_propArrow` / 引理 `succStruct_prop_le_propArrow`

English:
lemma succStruct_prop_le_propArrow
  proof: by
  have := locallySmall I κ
  have := isSmall I κ
  have := hasColimitsOfShape_discrete I κ
  have := hasPushouts I κ
  intro _ _ _ ⟨F⟩ f
  constructor
  · nth_rw 1 [← I.ofHoms_homFamily]
    apply pushouts_mk _ (functorObj_isPushout I.homFamily (F.obj f).hom)
    exact coproducts_of_small _ _ (co

中文:
引理 succStruct_prop_le_propArrow
  证明: by
  have := locallySmall I κ
  have := isSmall I κ
  have := hasColimitsOfShape_discrete I κ
  have := hasPushouts I κ
  intro _ _ _ ⟨F⟩ f
  constructor
  · nth_rw 1 [← I.ofHoms_homFamily]
    apply pushouts_mk _ (functorObj_isPushout I.homFamily (F.obj f).hom)
    exact coproducts_of_small _ _ (co

Depends on / 依赖: F.obj, I.homFamily, I.ofHoms_homFamily, MorphismProperty, MorphismProperty.isomorphisms.iff, colimitsOfShape_colimMap, coproducts_of_small, functorObj_isPushout, hasColimitsOfShape_discrete, hasPushouts, homFamily, infer_instance, isSmall, isomorphisms, locallySmall, nth_rw, ofHoms_homFamily, pushouts_mk, succStruct
-/
lemma succStruct_prop_le_propArrow :
    (succStruct I κ).prop <= (propArrow.{w} I).functorCategory (Arrow C) := by
  have := locallySmall I κ
  have := isSmall I κ
  have := hasColimitsOfShape_discrete I κ
  have := hasPushouts I κ
  intro _ _ _ ⟨F⟩ f
  constructor
  · nth_rw 1 [← I.ofHoms_homFamily]
    apply pushouts_mk _ (functorObj_isPushout I.homFamily (F.obj f).hom)
    exact coproducts_of_small _ _ (colimitsOfShape_colimMap _ (by rintro ⟨j⟩; constructor))
  · rw [MorphismProperty.isomorphisms.iff]
    dsimp [succStruct]
    infer_instance

/--
Definition of `iterationFunctor` / `iterationFunctor` 的定义

English:
definition iterationFunctor
  signature: : κ.ord.ToType ⥤ Arrow C ⥤ Arrow C
  body: haveI := hasIterationOfShape I κ
  (succStruct I κ).iterationFunctor κ.ord.ToType

中文:
定义 iterationFunctor
  签名: : κ.ord.ToType ⥤ 箭头 C ⥤ 箭头 C
  定义体: haveI := hasIterationOfShape I κ
  (succStruct I κ).iterationFunctor κ.ord.ToType

Depends on / 依赖: ToType, hasIterationOfShape, iterationFunctor, ord.ToType, succStruct
-/
noncomputable def iterationFunctor : κ.ord.ToType ⥤ Arrow C ⥤ Arrow C :=
  haveI := hasIterationOfShape I κ
  (succStruct I κ).iterationFunctor κ.ord.ToType

/--
Definition of `iteration` / `iteration` 的定义

English:
definition iteration
  signature: : Arrow C ⥤ Arrow C
  body: haveI := hasIterationOfShape I κ
  (succStruct I κ).iteration κ.ord.ToType

中文:
定义 iteration
  签名: : 箭头 C ⥤ 箭头 C
  定义体: haveI := hasIterationOfShape I κ
  (succStruct I κ).iteration κ.ord.ToType

Depends on / 依赖: ToType, hasIterationOfShape, iteration, ord.ToType, succStruct
-/
noncomputable def iteration : Arrow C ⥤ Arrow C :=
  haveI := hasIterationOfShape I κ
  (succStruct I κ).iteration κ.ord.ToType

/--
Definition of `ιIteration` / `ιIteration` 的定义

English:
definition ιIteration
  signature: : 𝟭 _ ⟶ iteration I κ
  body: haveI := hasIterationOfShape I κ
  (succStruct I κ).ιIteration κ.ord.ToType

中文:
定义 ιIteration
  签名: : 𝟭 _ ⟶ iteration I κ
  定义体: haveI := hasIterationOfShape I κ
  (succStruct I κ).ιIteration κ.ord.ToType

Depends on / 依赖: ToType, hasIterationOfShape, ord.ToType, succStruct
-/
noncomputable def ιIteration : 𝟭 _ ⟶ iteration I κ :=
  haveI := hasIterationOfShape I κ
  (succStruct I κ).ιIteration κ.ord.ToType

/--
Definition of `transfiniteCompositionOfShapeSuccStructPropιIteration` / `transfiniteCompositionOfShapeSuccStructPropιIteration` 的定义

English:
definition transfiniteCompositionOfShapeSuccStructPropιIteration
  signature: :
  body: haveI := hasIterationOfShape I κ
  (succStruct I κ).transfiniteCompositionOfShapeιIteration κ.ord.ToType

@[simp]

中文:
定义 transfiniteCompositionOfShapeSuccStructPropιIteration
  签名: :
  定义体: haveI := hasIterationOfShape I κ
  (succStruct I κ).transfiniteCompositionOfShapeιIteration κ.ord.ToType

@[simp]

Depends on / 依赖: ToType, hasIterationOfShape, ord.ToType, succStruct
-/
noncomputable def transfiniteCompositionOfShapeSuccStructPropιIteration :
    (succStruct I κ).prop.TransfiniteCompositionOfShape κ.ord.ToType (ιIteration I κ) :=
  haveI := hasIterationOfShape I κ
  (succStruct I κ).transfiniteCompositionOfShapeιIteration κ.ord.ToType

@[simp]
/--
lemma `transfiniteCompositionOfShapeSuccStructPropιIteration_F` / 引理 `transfiniteCompositionOfShapeSuccStructPropιIteration_F`

English:
lemma transfiniteCompositionOfShapeSuccStructPropιIteration_F
  proof: rfl

中文:
引理 transfiniteCompositionOfShapeSuccStructPropιIteration_F
  证明: rfl
-/
lemma transfiniteCompositionOfShapeSuccStructPropιIteration_F :
    (transfiniteCompositionOfShapeSuccStructPropιIteration I κ).F =
      iterationFunctor I κ :=
  rfl

/--
Definition of `transfiniteCompositionOfShapeιIterationAppRight` / `transfiniteCompositionOfShapeιIterationAppRight` 的定义

English:
definition transfiniteCompositionOfShapeιIterationAppRight
  signature: (f : Arrow C)
  body: haveI := hasIterationOfShape I κ
  let h := transfiniteCompositionOfShapeSuccStructPropιIteration I κ
  { toTransfiniteCompositionOfShape :=
      h.toTransfiniteCompositionOfShape.map ((evaluation _ _).obj f ⋙ Arrow.rightFunc)
    map_mem j hj := ((succStruct_prop_le_propArrow I κ _ (h.map_mem j hj

中文:
定义 transfiniteCompositionOfShapeιIterationAppRight
  签名: (f : 箭头 C)
  定义体: haveI := hasIterationOfShape I κ
  let h := transfiniteCompositionOfShapeSuccStructPropιIteration I κ
  { toTransfiniteCompositionOfShape :=
      h.toTransfiniteCompositionOfShape.map ((evaluation _ _).obj f ⋙ Arrow.rightFunc)
    map_mem j hj := ((succStruct_prop_le_propArrow I κ _ (h.map_mem j hj

Depends on / 依赖: Arrow.rightFunc, evaluation, h.map_mem, h.toTransfiniteCompositionOfShape.map, hasIterationOfShape, map_mem, rightFunc, succStruct_prop_le_propArrow, toTransfiniteCompositionOfShape
-/
noncomputable def transfiniteCompositionOfShapeιIterationAppRight (f : Arrow C) :
    (isomorphisms C).TransfiniteCompositionOfShape κ.ord.ToType
      ((ιIteration I κ).app f).right :=
  haveI := hasIterationOfShape I κ
  let h := transfiniteCompositionOfShapeSuccStructPropιIteration I κ
  { toTransfiniteCompositionOfShape :=
      h.toTransfiniteCompositionOfShape.map ((evaluation _ _).obj f ⋙ Arrow.rightFunc)
    map_mem j hj := ((succStruct_prop_le_propArrow I κ _ (h.map_mem j hj)) f).2 }

instance (f : Arrow C) : IsIso ((ιIteration I κ).app f).right :=
  (transfiniteCompositionOfShapeιIterationAppRight I κ f).isIso

instance {j₁ j₂ : κ.ord.ToType} (φ : j₁ ⟶ j₂) (f : Arrow C) :
    IsIso (((iterationFunctor I κ).map φ).app f).right :=
  inferInstanceAs (IsIso ((transfiniteCompositionOfShapeιIterationAppRight I κ f).F.map φ))

/-- For any `f : Arrow C`, the object `((iteration I κ).obj f).right`
identifies to `f.right`. -/
@[simps! hom]
/--
Definition of `iterationObjRightIso` / `iterationObjRightIso` 的定义

English:
definition iterationObjRightIso
  signature: (f : Arrow C)
  body: asIso ((ιIteration I κ).app f).right

中文:
定义 iterationObjRightIso
  签名: (f : 箭头 C)
  定义体: asIso ((ιIteration I κ).app f).right
-/
noncomputable def iterationObjRightIso (f : Arrow C) :
    f.right ≅ ((iteration I κ).obj f).right :=
  asIso ((ιIteration I κ).app f).right

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `iterationFunctorObjObjRightIso` / `iterationFunctorObjObjRightIso` 的定义

English:
definition iterationFunctorObjObjRightIso
  signature: (f : Arrow C) (j : κ.ord.ToType)
  body: asIso ((transfiniteCompositionOfShapeιIterationAppRight I κ f).incl.app j) ≪≫
    (iterationObjRightIso I κ f).symm

中文:
定义 iterationFunctorObjObjRightIso
  签名: (f : 箭头 C) (j : κ.ord.ToType)
  定义体: asIso ((transfiniteCompositionOfShapeιIterationAppRight I κ f).incl.app j) ≪≫
    (iterationObjRightIso I κ f).symm

Depends on / 依赖: incl.app, iterationObjRightIso
-/
noncomputable def iterationFunctorObjObjRightIso (f : Arrow C) (j : κ.ord.ToType) :
    (((iterationFunctor I κ).obj j).obj f).right ≅ f.right :=
  asIso ((transfiniteCompositionOfShapeιIterationAppRight I κ f).incl.app j) ≪≫
    (iterationObjRightIso I κ f).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `iterationFunctorObjObjRightIso_ιIteration_app_right` / 引理 `iterationFunctorObjObjRightIso_ιIteration_app_right`

English:
lemma iterationFunctorObjObjRightIso_ιIteration_app_right
  given: (f : Arrow C) (j : κ.ord.ToType)
  proof: by
  simp [iterationFunctorObjObjRightIso, iterationObjRightIso]

中文:
引理 iterationFunctorObjObjRightIso_ιIteration_app_right
  条件: (f : 箭头 C) (j : κ.ord.ToType)
  证明: by
  simp [iterationFunctorObjObjRightIso, iterationObjRightIso]

Depends on / 依赖: iterationFunctorObjObjRightIso, iterationObjRightIso
-/
lemma iterationFunctorObjObjRightIso_ιIteration_app_right (f : Arrow C) (j : κ.ord.ToType) :
    (iterationFunctorObjObjRightIso I κ f j).hom ≫ ((ιIteration I κ).app f).right =
      (transfiniteCompositionOfShapeιIterationAppRight I κ f).incl.app j := by
  simp [iterationFunctorObjObjRightIso, iterationObjRightIso]

/--
lemma `prop_iterationFunctor_map_succ` / 引理 `prop_iterationFunctor_map_succ`

English:
lemma prop_iterationFunctor_map_succ
  given: (j : κ.ord.ToType)
  proof: by
  have := hasIterationOfShape I κ
  have := Cardinal.noMaxOrder (Fact.elim inferInstance : κ.IsRegular).aleph0_le
  exact (succStruct I κ).prop_iterationFunctor_map_succ j (not_isMax j)

中文:
引理 prop_iterationFunctor_map_succ
  条件: (j : κ.ord.ToType)
  证明: by
  have := hasIterationOfShape I κ
  have := Cardinal.noMaxOrder (Fact.elim inferInstance : κ.IsRegular).aleph0_le
  exact (succStruct I κ).prop_iterationFunctor_map_succ j (not_isMax j)

Depends on / 依赖: Cardinal, Cardinal.noMaxOrder, Fact.elim, IsRegular, aleph0_le, hasIterationOfShape, noMaxOrder, not_isMax, prop_iterationFunctor_map_succ, succStruct
-/
lemma prop_iterationFunctor_map_succ (j : κ.ord.ToType) :
    (succStruct I κ).prop ((iterationFunctor I κ).map (homOfLE (Order.le_succ j))) := by
  have := hasIterationOfShape I κ
  have := Cardinal.noMaxOrder (Fact.elim inferInstance : κ.IsRegular).aleph0_le
  exact (succStruct I κ).prop_iterationFunctor_map_succ j (not_isMax j)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `iterationFunctorMapSuccAppArrowIso` / `iterationFunctorMapSuccAppArrowIso` 的定义

English:
definition iterationFunctorMapSuccAppArrowIso
  signature: (f : Arrow C) (j : κ.ord.ToType)
  body: hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    Arrow.mk (((iterationFunctor I κ).map (homOfLE (Order.le_succ j))).app f) ≅
      (ε I.homFamily).app (((iterationFunctor I κ).obj j).obj f) :=
  have := hasIterationOfShape I κ
  have := Cardinal.noMaxOrder (Fact.elim inferInstance : κ

中文:
定义 iterationFunctorMapSuccAppArrowIso
  签名: (f : 箭头 C) (j : κ.ord.ToType)
  定义体: hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    Arrow.mk (((iterationFunctor I κ).map (homOfLE (Order.le_succ j))).app f) ≅
      (ε I.homFamily).app (((iterationFunctor I κ).obj j).obj f) :=
  have := hasIterationOfShape I κ
  have := Cardinal.noMaxOrder (Fact.elim inferInstance : κ

Depends on / 依赖: hasColimitsOfShape_discrete
-/
noncomputable def iterationFunctorMapSuccAppArrowIso (f : Arrow C) (j : κ.ord.ToType) :
    letI := hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    Arrow.mk (((iterationFunctor I κ).map (homOfLE (Order.le_succ j))).app f) ≅
      (ε I.homFamily).app (((iterationFunctor I κ).obj j).obj f) :=
  have := hasIterationOfShape I κ
  have := Cardinal.noMaxOrder (Fact.elim inferInstance : κ.IsRegular).aleph0_le
  Arrow.isoMk (Iso.refl _)
    (((evaluation _ _).obj f).mapIso
      ((succStruct I κ).iterationFunctorObjSuccIso j (not_isMax j))) (by
    have := NatTrans.congr_app ((succStruct I κ).iterationFunctor_map_succ j (not_isMax j)) f
    dsimp at this
    dsimp [iterationFunctor]
    rw [id_comp]; rw [this]; rw [assoc]; rw [Iso.inv_hom_id_app]; rw [comp_id]
    dsimp [succStruct])

@[simp]
/--
lemma `iterationFunctorMapSuccAppArrowIso_hom_left` / 引理 `iterationFunctorMapSuccAppArrowIso_hom_left`

English:
lemma iterationFunctorMapSuccAppArrowIso_hom_left
  given: (f : Arrow C) (j : κ.ord.ToType)
  proof: rfl

中文:
引理 iterationFunctorMapSuccAppArrowIso_hom_left
  条件: (f : 箭头 C) (j : κ.ord.ToType)
  证明: rfl
-/
lemma iterationFunctorMapSuccAppArrowIso_hom_left (f : Arrow C) (j : κ.ord.ToType) :
    (iterationFunctorMapSuccAppArrowIso I κ f j).hom.left = 𝟙 _ := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in -- Needed below
@[reassoc (attr := simp)]
/--
lemma `iterationFunctorMapSuccAppArrowIso_hom_right_right_comp` / 引理 `iterationFunctorMapSuccAppArrowIso_hom_right_right_comp`

English:
lemma iterationFunctorMapSuccAppArrowIso_hom_right_right_comp
  proof: by
  have := Arrow.rightFunc.congr_map ((iterationFunctorMapSuccAppArrowIso I κ f j).hom.w)
  dsimp at this ⊢
  rw [← cancel_epi (((iterationFunctor I κ).map (homOfLE (Order.le_succ j))).app f).right]; rw [← reassoc_of% this]; rw [comp_id]

中文:
引理 iterationFunctorMapSuccAppArrowIso_hom_right_right_comp
  证明: by
  have := Arrow.rightFunc.congr_map ((iterationFunctorMapSuccAppArrowIso I κ f j).hom.w)
  dsimp at this ⊢
  rw [← cancel_epi (((iterationFunctor I κ).map (homOfLE (Order.le_succ j))).app f).right]; rw [← reassoc_of% this]; rw [comp_id]

Depends on / 依赖: Arrow.rightFunc.congr_map, Order.le_succ, cancel_epi, comp_id, congr_map, hom.w, homOfLE, iterationFunctor, iterationFunctorMapSuccAppArrowIso, le_succ, reassoc_of, rightFunc
-/
lemma iterationFunctorMapSuccAppArrowIso_hom_right_right_comp
    (f : Arrow C) (j : κ.ord.ToType) :
    (iterationFunctorMapSuccAppArrowIso I κ f j).hom.right.right ≫
      (((iterationFunctor I κ).map (homOfLE (Order.le_succ j))).app f).right = 𝟙 _ := by
  have := Arrow.rightFunc.congr_map ((iterationFunctorMapSuccAppArrowIso I κ f j).hom.w)
  dsimp at this ⊢
  rw [← cancel_epi (((iterationFunctor I κ).map (homOfLE (Order.le_succ j))).app f).right]; rw [← reassoc_of% this]; rw [comp_id]

section

variable {X Y : C} (f : X ⟶ Y)

/--
Definition of `obj` / `obj` 的定义

English:
definition obj
  signature: : C
  body: ((iteration I κ).obj (Arrow.mk f)).left

中文:
定义 obj
  签名: : C
  定义体: ((iteration I κ).obj (Arrow.mk f)).left

Depends on / 依赖: Arrow.mk, iteration
-/
noncomputable def obj : C := ((iteration I κ).obj (Arrow.mk f)).left

/--
Definition of `ιObj` / `ιObj` 的定义

English:
definition ιObj
  signature: : X ⟶ obj I κ f
  body: ((ιIteration I κ).app (Arrow.mk f)).left

中文:
定义 ιObj
  签名: : X ⟶ obj I κ f
  定义体: ((ιIteration I κ).app (Arrow.mk f)).left

Depends on / 依赖: Arrow.mk
-/
noncomputable def ιObj : X ⟶ obj I κ f := ((ιIteration I κ).app (Arrow.mk f)).left

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `πObj` / `πObj` 的定义

English:
definition πObj
  signature: : obj I κ f ⟶ Y
  body: ((iteration I κ).obj (Arrow.mk f)).hom ≫ inv ((ιIteration I κ).app f).right

中文:
定义 πObj
  签名: : obj I κ f ⟶ Y
  定义体: ((iteration I κ).obj (Arrow.mk f)).hom ≫ inv ((ιIteration I κ).app f).right

Depends on / 依赖: Arrow.mk, iteration
-/
noncomputable def πObj : obj I κ f ⟶ Y :=
  ((iteration I κ).obj (Arrow.mk f)).hom ≫ inv ((ιIteration I κ).app f).right

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `πObj_ιIteration_app_right` / 引理 `πObj_ιIteration_app_right`

English:
lemma πObj_ιIteration_app_right
  proof: by simp [πObj]

中文:
引理 πObj_ιIteration_app_right
  证明: by simp [πObj]
-/
lemma πObj_ιIteration_app_right :
    πObj I κ f ≫ ((ιIteration I κ).app f).right =
      ((iteration I κ).obj (Arrow.mk f)).hom := by simp [πObj]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `ιObj_πObj` / 引理 `ιObj_πObj`

English:
lemma ιObj_πObj
  statement: ιObj I κ f ≫ πObj I κ f = f
  proof: by
  simp [ιObj, πObj]

中文:
引理 ιObj_πObj
  结论: ιObj I κ f ≫ πObj I κ f = f
  证明: by
  simp [ιObj, πObj]
-/
lemma ιObj_πObj : ιObj I κ f ≫ πObj I κ f = f := by
  simp [ιObj, πObj]

/--
Definition of `relativeCellComplexιObj` / `relativeCellComplexιObj` 的定义

English:
definition relativeCellComplexιObj
  signature: :
  body: by
  have := hasIterationOfShape I κ
  let h := transfiniteCompositionOfShapeSuccStructPropιIteration I κ
  exact
  { toTransfiniteCompositionOfShape :=
      h.toTransfiniteCompositionOfShape.map ((evaluation _ _).obj f ⋙ Arrow.leftFunc)
    attachCells j hj :=
      attachCellsOfSuccStructProp I κ

中文:
定义 relativeCellComplexιObj
  签名: :
  定义体: by
  have := hasIterationOfShape I κ
  let h := transfiniteCompositionOfShapeSuccStructPropιIteration I κ
  exact
  { toTransfiniteCompositionOfShape :=
      h.toTransfiniteCompositionOfShape.map ((evaluation _ _).obj f ⋙ Arrow.leftFunc)
    attachCells j hj :=
      attachCellsOfSuccStructProp I κ

Depends on / 依赖: Arrow.leftFunc, attachCells, attachCellsOfSuccStructProp, evaluation, h.map_mem, h.toTransfiniteCompositionOfShape.map, hasIterationOfShape, leftFunc, map_mem, toTransfiniteCompositionOfShape
-/
noncomputable def relativeCellComplexιObj :
    RelativeCellComplex.{w} (fun (_ : κ.ord.ToType) => I.homFamily)
      (ιObj I κ f) := by
  have := hasIterationOfShape I κ
  let h := transfiniteCompositionOfShapeSuccStructPropιIteration I κ
  exact
  { toTransfiniteCompositionOfShape :=
      h.toTransfiniteCompositionOfShape.map ((evaluation _ _).obj f ⋙ Arrow.leftFunc)
    attachCells j hj :=
      attachCellsOfSuccStructProp I κ (h.map_mem j hj) f }

/--
lemma `transfiniteCompositionsOfShape_ιObj` / 引理 `transfiniteCompositionsOfShape_ιObj`

English:
lemma transfiniteCompositionsOfShape_ιObj
  proof: ⟨((relativeCellComplexιObj I κ f).transfiniteCompositionOfShape).ofLE
    (by simp)⟩

中文:
引理 transfiniteCompositionsOfShape_ιObj
  证明: ⟨((relativeCellComplexιObj I κ f).transfiniteCompositionOfShape).ofLE
    (by simp)⟩

Depends on / 依赖: transfiniteCompositionOfShape
-/
lemma transfiniteCompositionsOfShape_ιObj :
    (coproducts.{w} I).pushouts.transfiniteCompositionsOfShape κ.ord.ToType
      (ιObj I κ f) :=
  ⟨((relativeCellComplexιObj I κ f).transfiniteCompositionOfShape).ofLE
    (by simp)⟩

/--
lemma `llp_rlp_ιObj` / 引理 `llp_rlp_ιObj`

English:
lemma llp_rlp_ιObj
  statement: I.rlp.llp (ιObj I κ f)
  proof: by
  apply I.transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp κ.ord.ToType
  apply transfiniteCompositionsOfShape_ιObj

中文:
引理 llp_rlp_ιObj
  结论: I.rlp.llp (ιObj I κ f)
  证明: by
  apply I.transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp κ.ord.ToType
  apply transfiniteCompositionsOfShape_ιObj

Depends on / 依赖: I.transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp, ToType, ord.ToType, transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp
-/
lemma llp_rlp_ιObj : I.rlp.llp (ιObj I κ f) := by
  apply I.transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp κ.ord.ToType
  apply transfiniteCompositionsOfShape_ιObj

/--
Definition of `relativeCellComplexιObjFObjSuccIso` / `relativeCellComplexιObjFObjSuccIso` 的定义

English:
definition relativeCellComplexιObjFObjSuccIso
  signature: (j : κ.ord.ToType)
  body: hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    (relativeCellComplexιObj I κ f).F.obj (Order.succ j) ≅
      functorObj I.homFamily (((iterationFunctor I κ).obj j).obj (Arrow.mk f)).hom :=
  (Arrow.rightFunc ⋙ Arrow.leftFunc).mapIso
    (iterationFunctorMapSuccAppArrowIso I κ f j)

中文:
定义 relativeCellComplexιObjFObjSuccIso
  签名: (j : κ.ord.ToType)
  定义体: hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    (relativeCellComplexιObj I κ f).F.obj (Order.succ j) ≅
      functorObj I.homFamily (((iterationFunctor I κ).obj j).obj (Arrow.mk f)).hom :=
  (Arrow.rightFunc ⋙ Arrow.leftFunc).mapIso
    (iterationFunctorMapSuccAppArrowIso I κ f j)

Depends on / 依赖: hasColimitsOfShape_discrete
-/
noncomputable def relativeCellComplexιObjFObjSuccIso (j : κ.ord.ToType) :
    letI := hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    (relativeCellComplexιObj I κ f).F.obj (Order.succ j) ≅
      functorObj I.homFamily (((iterationFunctor I κ).obj j).obj (Arrow.mk f)).hom :=
  (Arrow.rightFunc ⋙ Arrow.leftFunc).mapIso
    (iterationFunctorMapSuccAppArrowIso I κ f j)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `ιFunctorObj_eq` / 引理 `ιFunctorObj_eq`

English:
lemma ιFunctorObj_eq
  given: (j : κ.ord.ToType)
  proof: hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    ιFunctorObj I.homFamily (((iterationFunctor I κ).obj j).obj (Arrow.mk f)).hom =
      (relativeCellComplexιObj I κ f).F.map (homOfLE (Order.le_succ j)) ≫
        (relativeCellComplexιObjFObjSuccIso I κ f j).hom := by
  simpa using! Arro

中文:
引理 ιFunctorObj_eq
  条件: (j : κ.ord.ToType)
  证明: hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    ιFunctorObj I.homFamily (((iterationFunctor I κ).obj j).obj (Arrow.mk f)).hom =
      (relativeCellComplexιObj I κ f).F.map (homOfLE (Order.le_succ j)) ≫
        (relativeCellComplexιObjFObjSuccIso I κ f j).hom := by
  simpa using! Arro

Depends on / 依赖: hasColimitsOfShape_discrete
-/
lemma ιFunctorObj_eq (j : κ.ord.ToType) :
    letI := hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    ιFunctorObj I.homFamily (((iterationFunctor I κ).obj j).obj (Arrow.mk f)).hom =
      (relativeCellComplexιObj I κ f).F.map (homOfLE (Order.le_succ j)) ≫
        (relativeCellComplexιObjFObjSuccIso I κ f j).hom := by
  simpa using! Arrow.leftFunc.congr_map (iterationFunctorMapSuccAppArrowIso I κ f j).hom.w

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `πFunctorObj_eq` / 引理 `πFunctorObj_eq`

English:
lemma πFunctorObj_eq
  given: (j : κ.ord.ToType)
  proof: hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    πFunctorObj I.homFamily (((iterationFunctor I κ).obj j).obj (Arrow.mk f)).hom =
      (relativeCellComplexιObjFObjSuccIso I κ f j).inv ≫
      (relativeCellComplexιObj I κ f).incl.app (Order.succ j) ≫
      πObj I κ f ≫ (iterationFuncto

中文:
引理 πFunctorObj_eq
  条件: (j : κ.ord.ToType)
  证明: hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    πFunctorObj I.homFamily (((iterationFunctor I κ).obj j).obj (Arrow.mk f)).hom =
      (relativeCellComplexιObjFObjSuccIso I κ f j).inv ≫
      (relativeCellComplexιObj I κ f).incl.app (Order.succ j) ≫
      πObj I κ f ≫ (iterationFuncto

Depends on / 依赖: hasColimitsOfShape_discrete
-/
lemma πFunctorObj_eq (j : κ.ord.ToType) :
    letI := hasColimitsOfShape_discrete I κ
    letI := hasPushouts I κ
    πFunctorObj I.homFamily (((iterationFunctor I κ).obj j).obj (Arrow.mk f)).hom =
      (relativeCellComplexιObjFObjSuccIso I κ f j).inv ≫
      (relativeCellComplexιObj I κ f).incl.app (Order.succ j) ≫
      πObj I κ f ≫ (iterationFunctorObjObjRightIso I κ (Arrow.mk f) j).inv := by
  have h₁ := (iterationFunctorMapSuccAppArrowIso I κ f j).hom.right.w
  have h₂ := (transfiniteCompositionOfShapeSuccStructPropιIteration I κ).incl.naturality
    (homOfLE (Order.le_succ j))
  dsimp at h₁ h₂
  rw [comp_id] at h₂
  rw [← cancel_mono (iterationFunctorObjObjRightIso I κ (Arrow.mk f) j).hom]; rw [← cancel_mono ((ιIteration I κ).app f).right]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_assoc]; rw [πObj_ιIteration_app_right]; rw [iterationFunctorObjObjRightIso_ιIteration_app_right]; rw [← cancel_epi (relativeCellComplexιObjFObjSuccIso I κ f j).hom]; rw [Iso.hom_inv_id_assoc]
  dsimp [relativeCellComplexιObjFObjSuccIso,
    relativeCellComplexιObj, transfiniteCompositionOfShapeιIterationAppRight]
  simp only [reassoc_of% h₁, comp_id, comp_id, Arrow.w_mk_right, ← h₂,
    NatTrans.comp_app, Arrow.comp_right,
    iterationFunctorMapSuccAppArrowIso_hom_right_right_comp_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `hasRightLiftingProperty_πObj` / 引理 `hasRightLiftingProperty_πObj`

English:
lemma hasRightLiftingProperty_πObj
  given: {A B : C} (i : A ⟶ B) (hi : I i) (f : X ⟶ Y)
  proof: ⟨by
  have := hasColimitsOfShape_discrete I κ
  have := hasPushouts I κ
  have := preservesColimit I κ i hi _ (relativeCellComplexιObj I κ f)
  intro g b sq
  obtain ⟨j, t, ht⟩ := Types.jointly_surjective _
    (isColimitOfPreserves (coyoneda.obj (Opposite.op A))
      (relativeCellComplexιObj I κ f

中文:
引理 hasRightLiftingProperty_πObj
  条件: {A B : C} (i : A ⟶ B) (hi : I i) (f : X ⟶ Y)
  证明: ⟨by
  have := hasColimitsOfShape_discrete I κ
  have := hasPushouts I κ
  have := preservesColimit I κ i hi _ (relativeCellComplexιObj I κ f)
  intro g b sq
  obtain ⟨j, t, ht⟩ := Types.jointly_surjective _
    (isColimitOfPreserves (coyoneda.obj (Opposite.op A))
      (relativeCellComplexιObj I κ f

Depends on / 依赖: F.map, I.homFamily, Opposite, Opposite.op, Order.le_succ, Types.jointly_surjective, coyoneda, coyoneda.obj, hasColimitsOfShape_discrete, hasPushouts, homFamily, homOfLE, incl.app, isColimit, isColimitOfPreserves, jointly_surjective, le_succ, preservesColimit
-/
lemma hasRightLiftingProperty_πObj {A B : C} (i : A ⟶ B) (hi : I i) (f : X ⟶ Y) :
    HasLiftingProperty i (πObj I κ f) := ⟨by
  have := hasColimitsOfShape_discrete I κ
  have := hasPushouts I κ
  have := preservesColimit I κ i hi _ (relativeCellComplexιObj I κ f)
  intro g b sq
  obtain ⟨j, t, ht⟩ := Types.jointly_surjective _
    (isColimitOfPreserves (coyoneda.obj (Opposite.op A))
      (relativeCellComplexιObj I κ f).isColimit) g
  dsimp at g b sq t ht
  obtain ⟨l, hl₁, hl₂⟩ := ιFunctorObj_extension' I.homFamily
    ((relativeCellComplexιObj I κ f).incl.app j ≫ πObj I κ f)
    ((relativeCellComplexιObj I κ f).F.map (homOfLE (Order.le_succ j)))
    ((relativeCellComplexιObj I κ f).incl.app (Order.succ j) ≫ πObj I κ f) (by simp) (Iso.refl _)
    (iterationFunctorObjObjRightIso I κ (Arrow.mk f) j).symm
    (relativeCellComplexιObjFObjSuccIso I κ f j)
    (by dsimp; rw [ιFunctorObj_eq, id_comp])
    (by dsimp; rw [πFunctorObj_eq, assoc, Iso.hom_inv_id_assoc])
    (i := ⟨i, hi⟩) t b (by rw [reassoc_of% ht, sq.w]; dsimp)
  dsimp at hl₁
  exact ⟨⟨{
    l := l ≫ (relativeCellComplexιObj I κ f).incl.app (Order.succ j)
    fac_left := by simp [reassoc_of% hl₁, ← ht]
    fac_right := by rw [assoc, hl₂]
  }⟩⟩⟩

/--
lemma `rlp_πObj` / 引理 `rlp_πObj`

English:
lemma rlp_πObj
  statement: I.rlp (πObj I κ f)
  proof: fun _ _ _ hi => hasRightLiftingProperty_πObj _ _ _ hi _

中文:
引理 rlp_πObj
  结论: I.rlp (πObj I κ f)
  证明: fun _ _ _ hi => hasRightLiftingProperty_πObj _ _ _ hi _
-/
lemma rlp_πObj : I.rlp (πObj I κ f) :=
  fun _ _ _ hi => hasRightLiftingProperty_πObj _ _ _ hi _

end

/--
Definition of `objMap` / `objMap` 的定义

English:
definition objMap
  signature: {f g : Arrow C} (φ : f ⟶ g)
  body: ((iteration I κ).map φ).left

@[simp]

中文:
定义 objMap
  签名: {f g : 箭头 C} (φ : f ⟶ g)
  定义体: ((iteration I κ).map φ).left

@[simp]

Depends on / 依赖: iteration
-/
noncomputable def objMap {f g : Arrow C} (φ : f ⟶ g) : obj I κ f.hom ⟶ obj I κ g.hom :=
  ((iteration I κ).map φ).left

@[simp]
/--
lemma `objMap_id` / 引理 `objMap_id`

English:
lemma objMap_id
  given: (f : Arrow C)
  statement: objMap I κ (𝟙 f) = 𝟙 _
  proof: by
  simp only [objMap, Functor.map_id]
  rfl

@[reassoc, simp]

中文:
引理 objMap_id
  条件: (f : 箭头 C)
  结论: objMap I κ (𝟙 f) = 𝟙 _
  证明: by
  simp only [objMap, Functor.map_id]
  rfl

@[reassoc, simp]

Depends on / 依赖: Functor, Functor.map_id, map_id, objMap
-/
lemma objMap_id (f : Arrow C) : objMap I κ (𝟙 f) = 𝟙 _ := by
  simp only [objMap, Functor.map_id]
  rfl

@[reassoc, simp]
/--
lemma `objMap_comp` / 引理 `objMap_comp`

English:
lemma objMap_comp
  given: {f g h : Arrow C} (φ : f ⟶ g) (ψ : g ⟶ h)
  proof: by
  simp only [objMap, Functor.map_comp]
  rfl

@[reassoc (attr := simp)]

中文:
引理 objMap_comp
  条件: {f g h : 箭头 C} (φ : f ⟶ g) (ψ : g ⟶ h)
  证明: by
  simp only [objMap, Functor.map_comp]
  rfl

@[reassoc (attr := simp)]

Depends on / 依赖: Functor, Functor.map_comp, map_comp, objMap
-/
lemma objMap_comp {f g h : Arrow C} (φ : f ⟶ g) (ψ : g ⟶ h) :
    objMap I κ (φ ≫ ψ) = objMap I κ φ ≫ objMap I κ ψ := by
  simp only [objMap, Functor.map_comp]
  rfl

@[reassoc (attr := simp)]
/--
lemma `ιObj_naturality` / 引理 `ιObj_naturality`

English:
lemma ιObj_naturality
  given: {f g : Arrow C} (φ : f ⟶ g)
  proof: Arrow.leftFunc.congr_map ((ιIteration I κ).naturality φ).symm

中文:
引理 ιObj_naturality
  条件: {f g : 箭头 C} (φ : f ⟶ g)
  证明: Arrow.leftFunc.congr_map ((ιIteration I κ).naturality φ).symm

Depends on / 依赖: Arrow.leftFunc.congr_map, congr_map, leftFunc, naturality
-/
lemma ιObj_naturality {f g : Arrow C} (φ : f ⟶ g) :
    ιObj I κ f.hom ≫ objMap I κ φ = φ.left ≫ ιObj I κ g.hom :=
  Arrow.leftFunc.congr_map ((ιIteration I κ).naturality φ).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `πObj_naturality` / 引理 `πObj_naturality`

English:
lemma πObj_naturality
  given: {f g : Arrow C} (φ : f ⟶ g)
  proof: by
  let e₁ := asIso ((ιIteration I κ).app (Arrow.mk f.hom)).right
  let e₂ := asIso ((ιIteration I κ).app (Arrow.mk g.hom)).right
  change _ ≫ _ ≫ e₂.inv = (_ ≫ e₁.inv) ≫ _
  have h₁ := ((iteration I κ).map φ).w =≫ e₂.inv
  have h₂ : φ.right ≫ e₂.hom = e₁.hom ≫ ((iteration I κ).map φ).right :=
    

中文:
引理 πObj_naturality
  条件: {f g : 箭头 C} (φ : f ⟶ g)
  证明: by
  let e₁ := asIso ((ιIteration I κ).app (Arrow.mk f.hom)).right
  let e₂ := asIso ((ιIteration I κ).app (Arrow.mk g.hom)).right
  change _ ≫ _ ≫ e₂.inv = (_ ≫ e₁.inv) ≫ _
  have h₁ := ((iteration I κ).map φ).w =≫ e₂.inv
  have h₂ : φ.right ≫ e₂.hom = e₁.hom ≫ ((iteration I κ).map φ).right :=
    

Depends on / 依赖: Arrow.mk, Arrow.rightFunc, Functor, Functor.whiskerRight, cancel_mono, f.hom, g.hom, inv_hom_id, inv_hom_id_assoc, iteration, naturality, rightFunc, whiskerRight
-/
lemma πObj_naturality {f g : Arrow C} (φ : f ⟶ g) :
    objMap I κ φ ≫ πObj I κ g.hom = πObj I κ f.hom ≫ φ.right := by
  let e₁ := asIso ((ιIteration I κ).app (Arrow.mk f.hom)).right
  let e₂ := asIso ((ιIteration I κ).app (Arrow.mk g.hom)).right
  change _ ≫ _ ≫ e₂.inv = (_ ≫ e₁.inv) ≫ _
  have h₁ := ((iteration I κ).map φ).w =≫ e₂.inv
  have h₂ : φ.right ≫ e₂.hom = e₁.hom ≫ ((iteration I κ).map φ).right :=
    ((Functor.whiskerRight (ιIteration I κ) Arrow.rightFunc).naturality φ)
  dsimp at h₁
  rw [assoc] at h₁
  apply h₁.trans
  simp only [← cancel_mono e₂.hom, assoc, e₂.inv_hom_id, h₂, e₁.inv_hom_id_assoc]
  rw [← assoc]
  apply comp_id

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functorial factorization `ιObj I κ f ≫ πObj I κ f.hom = f`
with `ιObj I κ f` in `I.rlp.llp` and `πObj I κ f.hom` in `I.rlp`. -/
@[simps]
/--
Definition of `functorialFactorizationData` / `functorialFactorizationData` 的定义

English:
definition functorialFactorizationData
  signature: :
  body: { obj f := obj I κ f.hom
      map φ := objMap I κ φ }
  i := { app f := ιObj I κ f.hom }
  p := { app f := πObj I κ f.hom }
  hi f := llp_rlp_ιObj I κ f.hom
  hp f := rlp_πObj I κ f.hom

中文:
定义 functorialFactorizationData
  签名: :
  定义体: { obj f := obj I κ f.hom
      map φ := objMap I κ φ }
  i := { app f := ιObj I κ f.hom }
  p := { app f := πObj I κ f.hom }
  hi f := llp_rlp_ιObj I κ f.hom
  hp f := rlp_πObj I κ f.hom

Depends on / 依赖: f.hom, objMap
-/
noncomputable def functorialFactorizationData :
    FunctorialFactorizationData I.rlp.llp I.rlp where
  Z :=
    { obj f := obj I κ f.hom
      map φ := objMap I κ φ }
  i := { app f := ιObj I κ f.hom }
  p := { app f := πObj I κ f.hom }
  hi f := llp_rlp_ιObj I κ f.hom
  hp f := rlp_πObj I κ f.hom

/--
lemma `hasFunctorialFactorization` / 引理 `hasFunctorialFactorization`

English:
lemma hasFunctorialFactorization
  proof: ⟨functorialFactorizationData I κ⟩

中文:
引理 hasFunctorialFactorization
  证明: ⟨functorialFactorizationData I κ⟩

Depends on / 依赖: functorialFactorizationData
-/
lemma hasFunctorialFactorization :
    HasFunctorialFactorization I.rlp.llp I.rlp where
  nonempty_functorialFactorizationData :=
    ⟨functorialFactorizationData I κ⟩

set_option backward.defeqAttrib.useBackward true in
/--
lemma `llp_rlp_of_isCardinalForSmallObjectArgument'` / 引理 `llp_rlp_of_isCardinalForSmallObjectArgument'`

English:
lemma llp_rlp_of_isCardinalForSmallObjectArgument'
  proof: by
  refine le_antisymm ?_
    (retracts_transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp I κ.ord.ToType)
  intro X Y f hf
  have sq : CommSq (ιObj I κ f) f (πObj I κ f) (𝟙 _) := ⟨by simp⟩
  have := hf _ (rlp_πObj I κ f)
  refine ⟨_, _, _, ?_, transfiniteCompositionsOfShape_ιObj I κ f⟩


中文:
引理 llp_rlp_of_isCardinalForSmallObjectArgument'
  证明: by
  refine le_antisymm ?_
    (retracts_transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp I κ.ord.ToType)
  intro X Y f hf
  have sq : CommSq (ιObj I κ f) f (πObj I κ f) (𝟙 _) := ⟨by simp⟩
  have := hf _ (rlp_πObj I κ f)
  refine ⟨_, _, _, ?_, transfiniteCompositionsOfShape_ιObj I κ f⟩


Depends on / 依赖: Arrow.homMk, CommSq, ToType, le_antisymm, ord.ToType, retracts_transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp, sq.lift
-/
lemma llp_rlp_of_isCardinalForSmallObjectArgument' :
    I.rlp.llp = (transfiniteCompositionsOfShape
      (coproducts.{w} I).pushouts κ.ord.ToType).retracts := by
  refine le_antisymm ?_
    (retracts_transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp I κ.ord.ToType)
  intro X Y f hf
  have sq : CommSq (ιObj I κ f) f (πObj I κ f) (𝟙 _) := ⟨by simp⟩
  have := hf _ (rlp_πObj I κ f)
  refine ⟨_, _, _, ?_, transfiniteCompositionsOfShape_ιObj I κ f⟩
  exact
    { i := Arrow.homMk (𝟙 _) sq.lift
      r := Arrow.homMk (𝟙 _) (πObj I κ f) }

omit κ in
attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType in
/--
lemma `llp_rlp_of_isCardinalForSmallObjectArgument_aleph0` / 引理 `llp_rlp_of_isCardinalForSmallObjectArgument_aleph0`

English:
lemma llp_rlp_of_isCardinalForSmallObjectArgument_aleph0
  proof: by
  let e : Nat ≃o Cardinal.aleph0.{w}.ord.ToType :=
    ULift.orderIso.{w}.symm.trans
      (OrderIso.ofRelIsoLT (Nonempty.some (by simp [← Ordinal.type_eq])))
  rw [SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument' _ Cardinal.aleph0]; rw [MorphismProperty.transfiniteCompositionsOfShape_eq_

中文:
引理 llp_rlp_of_isCardinalForSmallObjectArgument_aleph0
  证明: by
  let e : Nat ≃o Cardinal.aleph0.{w}.ord.ToType :=
    ULift.orderIso.{w}.symm.trans
      (OrderIso.ofRelIsoLT (Nonempty.some (by simp [← Ordinal.type_eq])))
  rw [SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument' _ Cardinal.aleph0]; rw [MorphismProperty.transfiniteCompositionsOfShape_eq_

Depends on / 依赖: Cardinal, Cardinal.aleph0, MorphismProperty, MorphismProperty.transfiniteCompositionsOfShape_eq_of_orderIso, Nonempty, Nonempty.some, OrderIso, OrderIso.ofRelIsoLT, Ordinal, Ordinal.type_eq, SmallObject, SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument, ToType, ULift.orderIso, aleph0, llp_rlp_of_isCardinalForSmallObjectArgument, ofRelIsoLT, ord.ToType, orderIso, symm.trans
-/
lemma llp_rlp_of_isCardinalForSmallObjectArgument_aleph0
    [I.IsCardinalForSmallObjectArgument Cardinal.aleph0.{w}] :
    I.rlp.llp = (transfiniteCompositionsOfShape (coproducts.{w} I).pushouts Nat).retracts := by
  let e : Nat ≃o Cardinal.aleph0.{w}.ord.ToType :=
    ULift.orderIso.{w}.symm.trans
      (OrderIso.ofRelIsoLT (Nonempty.some (by simp [← Ordinal.type_eq])))
  rw [SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument' _ Cardinal.aleph0]; rw [MorphismProperty.transfiniteCompositionsOfShape_eq_of_orderIso _ e]

/--
lemma `llp_rlp_of_isCardinalForSmallObjectArgument` / 引理 `llp_rlp_of_isCardinalForSmallObjectArgument`

English:
lemma llp_rlp_of_isCardinalForSmallObjectArgument
  proof: by
  refine le_antisymm ?_
    (retracts_transfiniteComposition_pushouts_coproducts_le_llp_rlp I)
  rw [llp_rlp_of_isCardinalForSmallObjectArgument' I κ]
  apply retracts_monotone
  apply transfiniteCompositionsOfShape_le_transfiniteCompositions

中文:
引理 llp_rlp_of_isCardinalForSmallObjectArgument
  证明: by
  refine le_antisymm ?_
    (retracts_transfiniteComposition_pushouts_coproducts_le_llp_rlp I)
  rw [llp_rlp_of_isCardinalForSmallObjectArgument' I κ]
  apply retracts_monotone
  apply transfiniteCompositionsOfShape_le_transfiniteCompositions

Depends on / 依赖: le_antisymm, llp_rlp_of_isCardinalForSmallObjectArgument, retracts_monotone, retracts_transfiniteComposition_pushouts_coproducts_le_llp_rlp, transfiniteCompositionsOfShape_le_transfiniteCompositions
-/
lemma llp_rlp_of_isCardinalForSmallObjectArgument :
    I.rlp.llp =
      (transfiniteCompositions.{w} (coproducts.{w} I).pushouts).retracts := by
  refine le_antisymm ?_
    (retracts_transfiniteComposition_pushouts_coproducts_le_llp_rlp I)
  rw [llp_rlp_of_isCardinalForSmallObjectArgument' I κ]
  apply retracts_monotone
  apply transfiniteCompositionsOfShape_le_transfiniteCompositions

end SmallObject

end CategoryTheory
