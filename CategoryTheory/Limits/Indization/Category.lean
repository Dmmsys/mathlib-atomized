/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Indization.Equalizers
public import Mathlib.CategoryTheory.Limits.Indization.LocallySmall
public import Mathlib.CategoryTheory.Limits.Indization.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Presheaf

/-!
# The category of Ind-objects

We define the `v`-category of Ind-objects of a category `C`, called `Ind C`, as well as the functors
`Ind.yoneda : C ⥤ Ind C` and `Ind.inclusion C : Ind C ⥤ Cᵒᵖ ⥤ Type v`.

For a small filtered category `I`, we also define `Ind.lim I : (I ⥤ C) ⥤ Ind C` and show that
it preserves finite limits and finite colimits.

This file will mainly collect results about ind-objects (stated in terms of `IsIndObject`) and
reinterpret them in terms of `Ind C`.

Adopting the theorem numbering of [Kashiwara2006], we show the following properties:

Limits:
* If `C` has products indexed by `α`, then `Ind C` has products indexed by `α`, and the functor
  `Ind C ⥤ Cᵒᵖ ⥤ Type v` creates such products (6.1.17),
* if `C` has equalizers, then `Ind C` has equalizers, and the functor `Ind C ⥤ Cᵒᵖ ⥤ Type v`
  creates them (6.1.17)
* if `C` has small limits (resp. finite limits), then `Ind C` has small limits (resp. finite limits)
  and the functor `Ind C ⥤ Cᵒᵖ ⥤ Type v` creates them (6.1.17),
* the functor `C ⥤ Ind C` preserves small limits (6.1.17).

Colimits:
* `Ind C` has filtered colimits (6.1.8), and the functor `Ind C ⥤ Cᵒᵖ ⥤ Type v` preserves filtered
  colimits,
* if `C` has coproducts indexed by a finite type `α`, then `Ind C` has coproducts indexed by `α`
  (6.1.18(ii)),
* if `C` has finite coproducts, then `Ind C` has small coproducts (6.1.18(ii)),
* if `C` has coequalizers, then `Ind C` has coequalizers (6.1.18(i)),
* if `C` has finite colimits, then `Ind C` has small colimits (6.1.18(iii)).
* `C ⥤ Ind C` preserves finite colimits (6.1.6),

Note that:
* the functor `Ind C ⥤ Cᵒᵖ ⥤ Type v` does not preserve any kind of colimit in general except for
  filtered colimits and
* the functor `C ⥤ Ind C` preserves finite colimits, but not infinite colimits in general.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Chapter 6
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]

variable (C) in
/--
Definition of `Ind` / `Ind` 的定义

English:
definition Ind
  signature: : Type (max u (v + 1))
  body: ShrinkHoms (ObjectProperty.FullSubcategory (IsIndObject (C := C)))

中文:
定义 Ind
  签名: : 类型 (最大值 u (v + 1))
  定义体: ShrinkHoms (ObjectProperty.FullSubcategory (IsIndObject (C := C)))

Depends on / 依赖: FullSubcategory, IsIndObject, ObjectProperty, ObjectProperty.FullSubcategory, ShrinkHoms
-/
def Ind : Type (max u (v + 1)) :=
  ShrinkHoms (ObjectProperty.FullSubcategory (IsIndObject (C := C)))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category.{v} (Ind C)
  body: inferInstanceAs Category.{v}
    (ShrinkHoms (ObjectProperty.FullSubcategory (IsIndObject (C := C))))

中文:
实例 :
  签名: 范畴.{v} (Ind C)
  定义体: inferInstanceAs Category.{v}
    (ShrinkHoms (ObjectProperty.FullSubcategory (IsIndObject (C := C))))

Depends on / 依赖: Category, FullSubcategory, IsIndObject, ObjectProperty, ObjectProperty.FullSubcategory, ShrinkHoms
-/
noncomputable instance : Category.{v} (Ind C) :=
inferInstanceAs Category.{v}
    (ShrinkHoms (ObjectProperty.FullSubcategory (IsIndObject (C := C))))

variable (C) in
/--
Definition of `Ind.equivalence` / `Ind.equivalence` 的定义

English:
definition Ind.equivalence
  signature: :
  body: (ShrinkHoms.equivalence _).symm

中文:
定义 Ind.equivalence
  签名: :
  定义体: (ShrinkHoms.equivalence _).symm
-/
noncomputable def Ind.equivalence :
    Ind C ≌ ObjectProperty.FullSubcategory (IsIndObject (C := C)) :=
  (ShrinkHoms.equivalence _).symm

variable (C) in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def Ind.inclusion
  body: (Ind.equivalence C).functor ⋙ ObjectProperty.ι _

中文:
定义 noncomputable
  签名: def Ind.inclusion
  定义体: (Ind.equivalence C).functor ⋙ ObjectProperty.ι _
-/
protected noncomputable def Ind.inclusion : Ind C ⥤ Cᵒᵖ ⥤ Type v :=
  (Ind.equivalence C).functor ⋙ ObjectProperty.ι _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Ind.inclusion C).Full
  body: inferInstanceAs ((Ind.equivalence C).functor ⋙ ObjectProperty.ι _).Full

中文:
实例 :
  签名: (Ind.inclusion C).满
  定义体: inferInstanceAs ((Ind.equivalence C).functor ⋙ ObjectProperty.ι _).Full

Depends on / 依赖: Ind.equivalence, ObjectProperty, equivalence, functor
-/
instance : (Ind.inclusion C).Full :=
inferInstanceAs ((Ind.equivalence C).functor ⋙ ObjectProperty.ι _).Full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Ind.inclusion C).Faithful
  body: inferInstanceAs ((Ind.equivalence C).functor ⋙ ObjectProperty.ι _).Faithful

中文:
实例 :
  签名: (Ind.inclusion C).忠实
  定义体: inferInstanceAs ((Ind.equivalence C).functor ⋙ ObjectProperty.ι _).Faithful

Depends on / 依赖: Faithful, Ind.equivalence, ObjectProperty, equivalence, functor
-/
instance : (Ind.inclusion C).Faithful :=
inferInstanceAs ((Ind.equivalence C).functor ⋙ ObjectProperty.ι _).Faithful

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def Ind.inclusion.fullyFaithful
  body: .ofFullyFaithful _

中文:
定义 noncomputable
  签名: def Ind.inclusion.fullyFaithful
  定义体: .ofFullyFaithful _
-/
protected noncomputable def Ind.inclusion.fullyFaithful : (Ind.inclusion C).FullyFaithful :=
  .ofFullyFaithful _

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def Ind.yoneda
  body: ObjectProperty.lift _ CategoryTheory.yoneda isIndObject_yoneda ⋙ (Ind.equivalence C).inverse

中文:
定义 noncomputable
  签名: def Ind.yoneda
  定义体: ObjectProperty.lift _ CategoryTheory.yoneda isIndObject_yoneda ⋙ (Ind.equivalence C).inverse
-/
protected noncomputable def Ind.yoneda : C ⥤ Ind C :=
  ObjectProperty.lift _ CategoryTheory.yoneda isIndObject_yoneda ⋙ (Ind.equivalence C).inverse

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Ind.yoneda (C := C)).Full
  body: inferInstanceAs Functor.Full
    ObjectProperty.lift _ CategoryTheory.yoneda isIndObject_yoneda ⋙ (Ind.equivalence C).inverse

中文:
实例 :
  签名: (Ind.yoneda (C := C)).满
  定义体: inferInstanceAs Functor.Full
    ObjectProperty.lift _ CategoryTheory.yoneda isIndObject_yoneda ⋙ (Ind.equivalence C).inverse
-/
instance : (Ind.yoneda (C := C)).Full :=
inferInstanceAs Functor.Full
    ObjectProperty.lift _ CategoryTheory.yoneda isIndObject_yoneda ⋙ (Ind.equivalence C).inverse

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Ind.yoneda (C := C)).Faithful
  body: inferInstanceAs Functor.Faithful
    ObjectProperty.lift _ CategoryTheory.yoneda isIndObject_yoneda ⋙ (Ind.equivalence C).inverse

中文:
实例 :
  签名: (Ind.yoneda (C := C)).忠实
  定义体: inferInstanceAs Functor.Faithful
    ObjectProperty.lift _ CategoryTheory.yoneda isIndObject_yoneda ⋙ (Ind.equivalence C).inverse

Depends on / 依赖: Faithful
-/
instance : (Ind.yoneda (C := C)).Faithful :=
inferInstanceAs Functor.Faithful
    ObjectProperty.lift _ CategoryTheory.yoneda isIndObject_yoneda ⋙ (Ind.equivalence C).inverse

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def Ind.yoneda.fullyFaithful
  body: .ofFullyFaithful _

中文:
定义 noncomputable
  签名: def Ind.yoneda.fullyFaithful
  定义体: .ofFullyFaithful _
-/
protected noncomputable def Ind.yoneda.fullyFaithful : (Ind.yoneda (C := C)).FullyFaithful :=
  .ofFullyFaithful _

/--
Definition of `Ind.yonedaCompInclusion` / `Ind.yonedaCompInclusion` 的定义

English:
definition Ind.yonedaCompInclusion
  signature: : Ind.yoneda ⋙ Ind.inclusion C ≅ CategoryTheory.yoneda
  body: isoWhiskerLeft (ObjectProperty.lift _ _ _)
    (isoWhiskerRight (Ind.equivalence C).counitIso (ObjectProperty.ι _))

中文:
定义 Ind.yonedaCompInclusion
  签名: : Ind.yoneda ⋙ Ind.inclusion C ≅ 范畴论.yoneda
  定义体: isoWhiskerLeft (ObjectProperty.lift _ _ _)
    (isoWhiskerRight (Ind.equivalence C).counitIso (ObjectProperty.ι _))

Depends on / 依赖: Ind.equivalence, ObjectProperty, ObjectProperty.lift, counitIso, equivalence, isoWhiskerLeft, isoWhiskerRight
-/
noncomputable def Ind.yonedaCompInclusion : Ind.yoneda ⋙ Ind.inclusion C ≅ CategoryTheory.yoneda :=
  isoWhiskerLeft (ObjectProperty.lift _ _ _)
    (isoWhiskerRight (Ind.equivalence C).counitIso (ObjectProperty.ι _))

noncomputable instance {J : Type v} [SmallCategory J] [IsFiltered J] :
    ObjectProperty.IsClosedUnderColimitsOfShape (IsIndObject (C := C)) J :=
  .mk' (by
    rintro _ ⟨F, hF⟩
    exact isIndObject_colimit _ _ hF)

noncomputable instance {J : Type v} [SmallCategory J] [IsFiltered J] :
    CreatesColimitsOfShape J (Ind.inclusion C) :=
inferInstanceAs
    CreatesColimitsOfShape J ((Ind.equivalence C).functor ⋙ ObjectProperty.ι _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasFilteredColimits (Ind C)
  body: hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (Ind.inclusion C)

中文:
实例 :
  签名: HasFilteredColimits (Ind C)
  定义体: hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (Ind.inclusion C)

Depends on / 依赖: Ind.inclusion, hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape, inclusion
-/
instance : HasFilteredColimits (Ind C) where
  HasColimitsOfShape _ _ _ :=
    hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (Ind.inclusion C)

noncomputable instance {J : Type v} [HasLimitsOfShape (Discrete J) C] :
    ObjectProperty.IsClosedUnderLimitsOfShape (IsIndObject (C := C)) (Discrete J) :=
  .mk' (by
    rintro _ ⟨F, hF⟩
    exact isIndObject_limit_of_discrete_of_hasLimitsOfShape _ hF)

noncomputable instance {J : Type v} [HasLimitsOfShape (Discrete J) C] :
    CreatesLimitsOfShape (Discrete J) (Ind.inclusion C) :=
inferInstanceAs
    CreatesLimitsOfShape (Discrete J) ((Ind.equivalence C).functor ⋙ ObjectProperty.ι _)

instance {J : Type v} [HasLimitsOfShape (Discrete J) C] :
    HasLimitsOfShape (Discrete J) (Ind C) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (Ind.inclusion C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimitsOfShape
  signature: WalkingParallelPair C] :
  body: inferInstanceAs
    CreatesLimitsOfShape WalkingParallelPair
      ((Ind.equivalence C).functor ⋙ ObjectProperty.ι _)

中文:
实例 [有形状极限
  签名: WalkingParallelPair C] :
  定义体: inferInstanceAs
    CreatesLimitsOfShape WalkingParallelPair
      ((Ind.equivalence C).functor ⋙ ObjectProperty.ι _)

Depends on / 依赖: CreatesLimitsOfShape, Ind.equivalence, ObjectProperty, WalkingParallelPair, equivalence, functor
-/
noncomputable instance [HasLimitsOfShape WalkingParallelPair C] :
    CreatesLimitsOfShape WalkingParallelPair (Ind.inclusion C) :=
inferInstanceAs
    CreatesLimitsOfShape WalkingParallelPair
      ((Ind.equivalence C).functor ⋙ ObjectProperty.ι _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimitsOfShape
  signature: WalkingParallelPair C] :
  body: hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (Ind.inclusion C)

中文:
实例 [有形状极限
  签名: WalkingParallelPair C] :
  定义体: hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (Ind.inclusion C)

Depends on / 依赖: Ind.inclusion, hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape, inclusion
-/
instance [HasLimitsOfShape WalkingParallelPair C] :
    HasLimitsOfShape WalkingParallelPair (Ind C) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (Ind.inclusion C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteLimits
  signature: C] : CreatesFiniteLimits (Ind.inclusion C)
  body: letI _ : CreatesFiniteProducts (Ind.inclusion C) :=
    { creates _ _ := createsLimitsOfShapeOfEquiv (Discrete.equivalence Equiv.ulift) _ }
  createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts (Ind.inclusion C)

中文:
实例 [有有限极限
  签名: C] : 创造有限极限 (Ind.inclusion C)
  定义体: letI _ : CreatesFiniteProducts (Ind.inclusion C) :=
    { creates _ _ := createsLimitsOfShapeOfEquiv (Discrete.equivalence Equiv.ulift) _ }
  createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts (Ind.inclusion C)

Depends on / 依赖: CreatesFiniteProducts, Discrete, Discrete.equivalence, Equiv.ulift, Ind.inclusion, creates, createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts, createsLimitsOfShapeOfEquiv, equivalence, inclusion
-/
noncomputable instance [HasFiniteLimits C] : CreatesFiniteLimits (Ind.inclusion C) :=
  letI _ : CreatesFiniteProducts (Ind.inclusion C) :=
    { creates _ _ := createsLimitsOfShapeOfEquiv (Discrete.equivalence Equiv.ulift) _ }
  createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts (Ind.inclusion C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteLimits
  signature: C] : HasFiniteLimits (Ind C)
  body: hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits (Ind.inclusion C)

中文:
实例 [有有限极限
  签名: C] : 有有限极限 (Ind C)
  定义体: hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits (Ind.inclusion C)

Depends on / 依赖: Ind.inclusion, hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits, inclusion
-/
instance [HasFiniteLimits C] : HasFiniteLimits (Ind C) :=
  hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits (Ind.inclusion C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimits
  signature: C] : CreatesLimitsOfSize.{v, v} (Ind.inclusion C)
  body: createsLimitsOfSizeOfCreatesEqualizersAndProducts.{v, v} (Ind.inclusion C)

中文:
实例 [有极限
  签名: C] : CreatesLimitsOfSize.{v, v} (Ind.inclusion C)
  定义体: createsLimitsOfSizeOfCreatesEqualizersAndProducts.{v, v} (Ind.inclusion C)

Depends on / 依赖: Ind.inclusion, createsLimitsOfSizeOfCreatesEqualizersAndProducts, inclusion
-/
noncomputable instance [HasLimits C] : CreatesLimitsOfSize.{v, v} (Ind.inclusion C) :=
  createsLimitsOfSizeOfCreatesEqualizersAndProducts.{v, v} (Ind.inclusion C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimits
  signature: C] : HasLimits (Ind C)
  body: hasLimits_of_hasLimits_createsLimits (Ind.inclusion C)

中文:
实例 [有极限
  签名: C] : 有极限 (Ind C)
  定义体: hasLimits_of_hasLimits_createsLimits (Ind.inclusion C)

Depends on / 依赖: Ind.inclusion, hasLimits_of_hasLimits_createsLimits, inclusion
-/
instance [HasLimits C] : HasLimits (Ind C) :=
  hasLimits_of_hasLimits_createsLimits (Ind.inclusion C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimits (Ind.yoneda (C := C))
  body: letI _ : PreservesLimitsOfSize.{v, v} (Ind.yoneda ⋙ Ind.inclusion C) :=
    preservesLimits_of_natIso Ind.yonedaCompInclusion.symm
  preservesLimits_of_reflects_of_preserves Ind.yoneda (Ind.inclusion C)

中文:
实例 :
  签名: PreservesLimits (Ind.yoneda (C := C))
  定义体: letI _ : PreservesLimitsOfSize.{v, v} (Ind.yoneda ⋙ Ind.inclusion C) :=
    preservesLimits_of_natIso Ind.yonedaCompInclusion.symm
  preservesLimits_of_reflects_of_preserves Ind.yoneda (Ind.inclusion C)
-/
instance : PreservesLimits (Ind.yoneda (C := C)) :=
  letI _ : PreservesLimitsOfSize.{v, v} (Ind.yoneda ⋙ Ind.inclusion C) :=
    preservesLimits_of_natIso Ind.yonedaCompInclusion.symm
  preservesLimits_of_reflects_of_preserves Ind.yoneda (Ind.inclusion C)

/--
theorem `Ind.isIndObject_inclusion_obj` / 定理 `Ind.isIndObject_inclusion_obj`

English:
theorem Ind.isIndObject_inclusion_obj
  given: (X : Ind C)
  statement: IsIndObject ((Ind.inclusion C).obj X)
  proof: X.2

中文:
定理 Ind.isIndObject_inclusion_obj
  条件: (X : Ind C)
  结论: 是IndObject ((Ind.inclusion C).obj X)
  证明: X.2
-/
theorem Ind.isIndObject_inclusion_obj (X : Ind C) : IsIndObject ((Ind.inclusion C).obj X) :=
  X.2

/--
Definition of `Ind.presentation` / `Ind.presentation` 的定义

English:
definition Ind.presentation
  signature: (X : Ind C)
  body: X.isIndObject_inclusion_obj.presentation

中文:
定义 Ind.presentation
  签名: (X : Ind C)
  定义体: X.isIndObject_inclusion_obj.presentation

Depends on / 依赖: X.isIndObject_inclusion_obj.presentation, isIndObject_inclusion_obj, presentation
-/
noncomputable def Ind.presentation (X : Ind C) : IndObjectPresentation ((Ind.inclusion C).obj X) :=
  X.isIndObject_inclusion_obj.presentation

/--
Definition of `Ind.colimitPresentationCompYoneda` / `Ind.colimitPresentationCompYoneda` 的定义

English:
definition Ind.colimitPresentationCompYoneda
  signature: (X : Ind C)
  body: Ind.inclusion.fullyFaithful.isoEquiv.symm calc
    (Ind.inclusion C).obj (colimit (X.presentation.F ⋙ Ind.yoneda))
      ≅ colimit (X.presentation.F ⋙ Ind.yoneda ⋙ Ind.inclusion C) := preservesColimitIso _ _
    _ ≅ colimit (X.presentation.F ⋙ yoneda) :=
          HasColimit.isoOfNatIso (isoWhiskerLeft X.presentation.F Ind.yonedaCompInclusion)
    _ ≅ (Ind.inclusion C).obj X :=
          IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) X.presentation.isColimit

中文:
定义 Ind.colimitPresentationCompYoneda
  签名: (X : Ind C)
  定义体: Ind.inclusion.fullyFaithful.isoEquiv.symm calc
    (Ind.inclusion C).obj (colimit (X.presentation.F ⋙ Ind.yoneda))
      ≅ colimit (X.presentation.F ⋙ Ind.yoneda ⋙ Ind.inclusion C) := preservesColimitIso _ _
    _ ≅ colimit (X.presentation.F ⋙ yoneda) :=
          HasColimit.isoOfNatIso (isoWhiskerLeft X.presentation.F Ind.yonedaCompInclusion)
    _ ≅ (Ind.inclusion C).obj X :=
          IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) X.presentation.isColimit

Depends on / 依赖: HasColimit, HasColimit.isoOfNatIso, Ind.inclusion, Ind.inclusion.fullyFaithful.isoEquiv.symm, Ind.yoneda, Ind.yonedaCompInclusion, IsColimit, IsColimit.coconePointUniqueUpToIso, X.presentation.F, X.presentation.isColimit, coconePointUniqueUpToIso, colimit, colimit.isColimit, fullyFaithful, inclusion, isColimit, isoEquiv, isoOfNatIso, isoWhiskerLeft, presentation
-/
noncomputable def Ind.colimitPresentationCompYoneda (X : Ind C) :
    colimit (X.presentation.F ⋙ Ind.yoneda) ≅ X :=
Ind.inclusion.fullyFaithful.isoEquiv.symm calc
    (Ind.inclusion C).obj (colimit (X.presentation.F ⋙ Ind.yoneda))
      ≅ colimit (X.presentation.F ⋙ Ind.yoneda ⋙ Ind.inclusion C) := preservesColimitIso _ _
    _ ≅ colimit (X.presentation.F ⋙ yoneda) :=
          HasColimit.isoOfNatIso (isoWhiskerLeft X.presentation.F Ind.yonedaCompInclusion)
    _ ≅ (Ind.inclusion C).obj X :=
          IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) X.presentation.isColimit

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RepresentablyCoflat (Ind.yoneda (C := C))
  body: by
  refine ⟨fun X => ?_⟩
  suffices IsFiltered (CostructuredArrow yoneda ((Ind.inclusion C).obj X)) from
    IsFiltered.of_equivalence
      ((CostructuredArrow.post Ind.yoneda (Ind.inclusion C) X).asEquivalence.trans
      (CostructuredArrow.mapNatIso Ind.yonedaCompInclusion)).symm
  exact ((isIndObject_iff _).1 (Ind.isIndObject_inclusion_obj X)).1

中文:
实例 :
  签名: RepresentablyCoflat (Ind.yoneda (C := C))
  定义体: by
  refine ⟨fun X => ?_⟩
  suffices IsFiltered (CostructuredArrow yoneda ((Ind.inclusion C).obj X)) from
    IsFiltered.of_equivalence
      ((CostructuredArrow.post Ind.yoneda (Ind.inclusion C) X).asEquivalence.trans
      (CostructuredArrow.mapNatIso Ind.yonedaCompInclusion)).symm
  exact ((isIndObject_iff _).1 (Ind.isIndObject_inclusion_obj X)).1

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mapNatIso, CostructuredArrow.post, Ind.inclusion, Ind.isIndObject_inclusion_obj, Ind.yoneda, Ind.yonedaCompInclusion, IsFiltered, IsFiltered.of_equivalence, asEquivalence, asEquivalence.trans, inclusion, isIndObject_iff, isIndObject_inclusion_obj, mapNatIso, of_equivalence, yoneda, yonedaCompInclusion
-/
instance : RepresentablyCoflat (Ind.yoneda (C := C)) := by
  refine ⟨fun X => ?_⟩
  suffices IsFiltered (CostructuredArrow yoneda ((Ind.inclusion C).obj X)) from
    IsFiltered.of_equivalence
      ((CostructuredArrow.post Ind.yoneda (Ind.inclusion C) X).asEquivalence.trans
      (CostructuredArrow.mapNatIso Ind.yonedaCompInclusion)).symm
  exact ((isIndObject_iff _).1 (Ind.isIndObject_inclusion_obj X)).1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteColimits (Ind.yoneda (C := C))
  body: preservesFiniteColimits_of_coflat _

中文:
实例 :
  签名: 保持FiniteColimits (Ind.yoneda (C := C))
  定义体: preservesFiniteColimits_of_coflat _
-/
noncomputable instance : PreservesFiniteColimits (Ind.yoneda (C := C)) :=
  preservesFiniteColimits_of_coflat _

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def Ind.lim (I : Type v) [SmallCategory I] [IsFiltered I]
  body: (whiskeringRight _ _ _).obj Ind.yoneda ⋙ colim

中文:
定义 noncomputable
  签名: def Ind.lim (I : 类型v) [小范畴 I] [是Filtered I]
  定义体: (whiskeringRight _ _ _).obj Ind.yoneda ⋙ colim
-/
protected noncomputable def Ind.lim (I : Type v) [SmallCategory I] [IsFiltered I] :
    (I ⥤ C) ⥤ Ind C :=
  (whiskeringRight _ _ _).obj Ind.yoneda ⋙ colim

/--
Definition of `Ind.limCompInclusion` / `Ind.limCompInclusion` 的定义

English:
definition Ind.limCompInclusion
  signature: {I : Type v} [SmallCategory I] [IsFiltered I]
  body: calc
  Ind.lim I ⋙ Ind.inclusion C
    ≅ (whiskeringRight _ _ _).obj Ind.yoneda ⋙ colim ⋙ Ind.inclusion C := Functor.associator _ _ _
  _ ≅ (whiskeringRight _ _ _).obj Ind.yoneda ⋙
      (whiskeringRight _ _ _).obj (Ind.inclusion C) ⋙ colim :=
    isoWhiskerLeft _ (preservesColimitNatIso _)
  _ ≅ ((whiskeringRight _ _ _).obj Ind.yoneda ⋙
      (whiskeringRight _ _ _).obj (Ind.inclusion C)) ⋙ colim := (Functor.associator _ _ _).symm
  _ ≅ (whiskeringRight _ _ _).obj (Ind.yoneda ⋙ Ind.inclusion C) ⋙ colim :=
    isoWhiskerRight (whiskeringRightObjCompIso _ _) colim
  _ ≅ (whiskeringRight _ _ _).obj yoneda ⋙ colim :=
    isoWhiskerRight ((whiskeringRight _ _ _).mapIso (Ind.yonedaCompInclusion)) colim

中文:
定义 Ind.limCompInclusion
  签名: {I : 类型v} [小范畴 I] [是Filtered I]
  定义体: calc
  Ind.lim I ⋙ Ind.inclusion C
    ≅ (whiskeringRight _ _ _).obj Ind.yoneda ⋙ colim ⋙ Ind.inclusion C := Functor.associator _ _ _
  _ ≅ (whiskeringRight _ _ _).obj Ind.yoneda ⋙
      (whiskeringRight _ _ _).obj (Ind.inclusion C) ⋙ colim :=
    isoWhiskerLeft _ (preservesColimitNatIso _)
  _ ≅ ((whiskeringRight _ _ _).obj Ind.yoneda ⋙
      (whiskeringRight _ _ _).obj (Ind.inclusion C)) ⋙ colim := (Functor.associator _ _ _).symm
  _ ≅ (whiskeringRight _ _ _).obj (Ind.yoneda ⋙ Ind.inclusion C) ⋙ colim :=
    isoWhiskerRight (whiskeringRightObjCompIso _ _) colim
  _ ≅ (whiskeringRight _ _ _).obj yoneda ⋙ colim :=
    isoWhiskerRight ((whiskeringRight _ _ _).mapIso (Ind.yonedaCompInclusion)) colim
-/
noncomputable def Ind.limCompInclusion {I : Type v} [SmallCategory I] [IsFiltered I] :
    Ind.lim I ⋙ Ind.inclusion C ≅ (whiskeringRight _ _ _).obj yoneda ⋙ colim := calc
  Ind.lim I ⋙ Ind.inclusion C
    ≅ (whiskeringRight _ _ _).obj Ind.yoneda ⋙ colim ⋙ Ind.inclusion C := Functor.associator _ _ _
  _ ≅ (whiskeringRight _ _ _).obj Ind.yoneda ⋙
      (whiskeringRight _ _ _).obj (Ind.inclusion C) ⋙ colim :=
    isoWhiskerLeft _ (preservesColimitNatIso _)
  _ ≅ ((whiskeringRight _ _ _).obj Ind.yoneda ⋙
      (whiskeringRight _ _ _).obj (Ind.inclusion C)) ⋙ colim := (Functor.associator _ _ _).symm
  _ ≅ (whiskeringRight _ _ _).obj (Ind.yoneda ⋙ Ind.inclusion C) ⋙ colim :=
    isoWhiskerRight (whiskeringRightObjCompIso _ _) colim
  _ ≅ (whiskeringRight _ _ _).obj yoneda ⋙ colim :=
    isoWhiskerRight ((whiskeringRight _ _ _).mapIso (Ind.yonedaCompInclusion)) colim

instance {α : Type w} [SmallCategory α] [FinCategory α] [HasLimitsOfShape α C] {I : Type v}
    [SmallCategory I] [IsFiltered I] :
    PreservesLimitsOfShape α (Ind.lim I : (I ⥤ C) ⥤ _) :=
  haveI : PreservesLimitsOfShape α (Ind.lim I ⋙ Ind.inclusion C) :=
    preservesLimitsOfShape_of_natIso Ind.limCompInclusion.symm
  preservesLimitsOfShape_of_reflects_of_preserves _ (Ind.inclusion C)

instance {α : Type w} [SmallCategory α] [FinCategory α] [HasColimitsOfShape α C] {I : Type v}
    [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape α (Ind.lim I : (I ⥤ C) ⥤ _) :=
  inferInstanceAs (PreservesColimitsOfShape α (_ ⋙ colim))

instance {α : Type v} [Finite α] [HasColimitsOfShape (Discrete α) C] :
    HasColimitsOfShape (Discrete α) (Ind C) := by
  refine ⟨fun F => ?_⟩
  let I : α -> Type v := fun s => (F.obj ⟨s⟩).presentation.I
  let G : forall s, I s ⥤ C := fun s => (F.obj ⟨s⟩).presentation.F
  let iso : Discrete.functor (fun s => Pi.eval I s ⋙ G s) ⋙
      (whiskeringRight _ _ _).obj Ind.yoneda ⋙ colim ≅ F := by
    refine Discrete.natIso (fun s => ?_)
    refine (Functor.Final.colimitIso (Pi.eval I s.as) (G s.as ⋙ Ind.yoneda)) ≪≫ ?_
    exact Ind.colimitPresentationCompYoneda _
  -- The actual proof happens during typeclass resolution in the following line, which deduces
  -- ```
  -- HasColimit Discrete.functor (fun s => Pi.eval I s ⋙ G s) ⋙
  -- (whiskeringRight _ _ _).obj Ind.yoneda ⋙ colim
  -- ```
  -- from the fact that finite limits commute with filtered colimits and from the fact that
  -- `Ind.yoneda` preserves finite colimits.
  exact hasColimit_of_iso iso.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteCoproducts
  signature: C] : HasCoproducts.{v} (Ind C)
  body: have : HasFiniteCoproducts (Ind C) :=
    ⟨fun _ => hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift)⟩
  hasCoproducts_of_finite_and_filtered

中文:
实例 [有FiniteCoproducts
  签名: C] : HasCoproducts.{v} (Ind C)
  定义体: have : HasFiniteCoproducts (Ind C) :=
    ⟨fun _ => hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift)⟩
  hasCoproducts_of_finite_and_filtered

Depends on / 依赖: Discrete, Discrete.equivalence, Equiv.ulift, HasFiniteCoproducts, equivalence, hasColimitsOfShape_of_equivalence, hasCoproducts_of_finite_and_filtered
-/
instance [HasFiniteCoproducts C] : HasCoproducts.{v} (Ind C) :=
  have : HasFiniteCoproducts (Ind C) :=
    ⟨fun _ => hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift)⟩
  hasCoproducts_of_finite_and_filtered

/--
Definition of `IndParallelPairPresentation.parallelPairIsoParallelPairCompIndYoneda` / `IndParallelPairPresentation.parallelPairIsoParallelPairCompIndYoneda` 的定义

English:
definition IndParallelPairPresentation.parallelPairIsoParallelPairCompIndYoneda
  body: ((whiskeringRight WalkingParallelPair _ _).obj (Ind.inclusion C)).preimageIso
    diagramIsoParallelPair _ ≪≫
      P.parallelPairIsoParallelPairCompYoneda ≪≫
      isoWhiskerLeft (parallelPair _ _) Ind.limCompInclusion.symm

中文:
定义 IndParallelPairPresentation.parallelPairIsoParallelPairCompIndYoneda
  定义体: ((whiskeringRight WalkingParallelPair _ _).obj (Ind.inclusion C)).preimageIso
    diagramIsoParallelPair _ ≪≫
      P.parallelPairIsoParallelPairCompYoneda ≪≫
      isoWhiskerLeft (parallelPair _ _) Ind.limCompInclusion.symm

Depends on / 依赖: Ind.inclusion, Ind.limCompInclusion.symm, P.parallelPairIsoParallelPairCompYoneda, WalkingParallelPair, diagramIsoParallelPair, inclusion, isoWhiskerLeft, limCompInclusion, parallelPair, parallelPairIsoParallelPairCompYoneda, preimageIso, whiskeringRight
-/
noncomputable def IndParallelPairPresentation.parallelPairIsoParallelPairCompIndYoneda
    {A B : Ind C} {f g : A ⟶ B}
    (P : IndParallelPairPresentation ((Ind.inclusion _).map f) ((Ind.inclusion _).map g)) :
    parallelPair f g ≅ parallelPair P.φ P.ψ ⋙ Ind.lim P.I :=
((whiskeringRight WalkingParallelPair _ _).obj (Ind.inclusion C)).preimageIso
    diagramIsoParallelPair _ ≪≫
      P.parallelPairIsoParallelPairCompYoneda ≪≫
      isoWhiskerLeft (parallelPair _ _) Ind.limCompInclusion.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimitsOfShape
  signature: WalkingParallelPair C] :
  body: by
  refine ⟨fun F => ?_⟩
  obtain ⟨P⟩ := nonempty_indParallelPairPresentation (F.obj WalkingParallelPair.zero).2
    (F.obj WalkingParallelPair.one).2 (Ind.inclusion _ |>.map <| F.map WalkingParallelPairHom.left)
    (Ind.inclusion _ |>.map <| F.map WalkingParallelPairHom.right)
  exact hasColimit_of_iso (diagramIsoParallelPair _ ≪≫ P.parallelPairIsoParallelPairCompIndYoneda)

中文:
实例 [有形状余极限
  签名: WalkingParallelPair C] :
  定义体: by
  refine ⟨fun F => ?_⟩
  obtain ⟨P⟩ := nonempty_indParallelPairPresentation (F.obj WalkingParallelPair.zero).2
    (F.obj WalkingParallelPair.one).2 (Ind.inclusion _ |>.map <| F.map WalkingParallelPairHom.left)
    (Ind.inclusion _ |>.map <| F.map WalkingParallelPairHom.right)
  exact hasColimit_of_iso (diagramIsoParallelPair _ ≪≫ P.parallelPairIsoParallelPairCompIndYoneda)

Depends on / 依赖: F.map, F.obj, Ind.inclusion, P.parallelPairIsoParallelPairCompIndYoneda, WalkingParallelPair, WalkingParallelPair.one, WalkingParallelPair.zero, WalkingParallelPairHom, WalkingParallelPairHom.left, WalkingParallelPairHom.right, diagramIsoParallelPair, hasColimit_of_iso, inclusion, nonempty_indParallelPairPresentation, parallelPairIsoParallelPairCompIndYoneda
-/
instance [HasColimitsOfShape WalkingParallelPair C] :
    HasColimitsOfShape WalkingParallelPair (Ind C) := by
  refine ⟨fun F => ?_⟩
  obtain ⟨P⟩ := nonempty_indParallelPairPresentation (F.obj WalkingParallelPair.zero).2
    (F.obj WalkingParallelPair.one).2 (Ind.inclusion _ |>.map <| F.map WalkingParallelPairHom.left)
    (Ind.inclusion _ |>.map <| F.map WalkingParallelPairHom.right)
  exact hasColimit_of_iso (diagramIsoParallelPair _ ≪≫ P.parallelPairIsoParallelPairCompIndYoneda)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteColimits
  signature: C] : HasColimits (Ind C)
  body: has_colimits_of_hasCoequalizers_and_coproducts

中文:
实例 [有有限余极限
  签名: C] : 有余极限 (Ind C)
  定义体: has_colimits_of_hasCoequalizers_and_coproducts

Depends on / 依赖: has_colimits_of_hasCoequalizers_and_coproducts
-/
instance [HasFiniteColimits C] : HasColimits (Ind C) :=
  has_colimits_of_hasCoequalizers_and_coproducts

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Ind.exists_nonempty_arrow_mk_iso_ind_lim` / 定理 `Ind.exists_nonempty_arrow_mk_iso_ind_lim`

English:
theorem Ind.exists_nonempty_arrow_mk_iso_ind_lim
  given: {A B : Ind C} {f : A ⟶ B}
  proof: by
  obtain ⟨P⟩ := nonempty_indParallelPairPresentation A.2 B.2
    (Ind.inclusion _ |>.map f) (Ind.inclusion _ |>.map f)
  refine ⟨P.I, inferInstance, inferInstance, P.F₁, P.F₂, P.φ, ⟨Arrow.isoMk ?_ ?_ ?_⟩⟩
  · exact P.parallelPairIsoParallelPairCompIndYoneda.app WalkingParallelPair.zero
  · exact P.parallelPairIsoParallelPairCompIndYoneda.app WalkingParallelPair.one
  · simpa using!
      (P.parallelPairIsoParallelPairCompIndYoneda.hom.naturality WalkingParallelPairHom.left).symm

中文:
定理 Ind.存在_nonempty_arrow_mk_iso_ind_lim
  条件: {A B : Ind C} {f : A ⟶ B}
  证明: by
  obtain ⟨P⟩ := nonempty_indParallelPairPresentation A.2 B.2
    (Ind.inclusion _ |>.map f) (Ind.inclusion _ |>.map f)
  refine ⟨P.I, inferInstance, inferInstance, P.F₁, P.F₂, P.φ, ⟨Arrow.isoMk ?_ ?_ ?_⟩⟩
  · exact P.parallelPairIsoParallelPairCompIndYoneda.app WalkingParallelPair.zero
  · exact P.parallelPairIsoParallelPairCompIndYoneda.app WalkingParallelPair.one
  · simpa using!
      (P.parallelPairIsoParallelPairCompIndYoneda.hom.naturality WalkingParallelPairHom.left).symm

Depends on / 依赖: Arrow.isoMk, Ind.inclusion, P.parallelPairIsoParallelPairCompIndYoneda.app, P.parallelPairIsoParallelPairCompIndYoneda.hom.naturality, WalkingParallelPair, WalkingParallelPair.one, WalkingParallelPair.zero, WalkingParallelPairHom, WalkingParallelPairHom.left, inclusion, naturality, nonempty_indParallelPairPresentation, parallelPairIsoParallelPairCompIndYoneda
-/
theorem Ind.exists_nonempty_arrow_mk_iso_ind_lim {A B : Ind C} {f : A ⟶ B} :
    exists (I : Type v) (_ : SmallCategory I) (_ : IsFiltered I) (F G : I ⥤ C) (φ : F ⟶ G),
      Nonempty (Arrow.mk f ≅ Arrow.mk ((Ind.lim _).map φ)) := by
  obtain ⟨P⟩ := nonempty_indParallelPairPresentation A.2 B.2
    (Ind.inclusion _ |>.map f) (Ind.inclusion _ |>.map f)
  refine ⟨P.I, inferInstance, inferInstance, P.F₁, P.F₂, P.φ, ⟨Arrow.isoMk ?_ ?_ ?_⟩⟩
  · exact P.parallelPairIsoParallelPairCompIndYoneda.app WalkingParallelPair.zero
  · exact P.parallelPairIsoParallelPairCompIndYoneda.app WalkingParallelPair.one
  · simpa using!
      (P.parallelPairIsoParallelPairCompIndYoneda.hom.naturality WalkingParallelPairHom.left).symm

section Small

variable (C : Type u) [SmallCategory C] [HasFiniteColimits C]

/--
Definition of `Ind.leftExactFunctorEquivalence` / `Ind.leftExactFunctorEquivalence` 的定义

English:
definition Ind.leftExactFunctorEquivalence
  signature: : Ind C ≌ LeftExactFunctor Cᵒᵖ (Type u)
  body: (Ind.equivalence _).trans ObjectProperty.fullSubcategoryCongr
    (by ext; apply isIndObject_iff_preservesFiniteLimits)

中文:
定义 Ind.leftExactFunctorEquivalence
  签名: : Ind C ≌ LeftExactFunctor Cᵒᵖ (类型u)
  定义体: (Ind.equivalence _).trans ObjectProperty.fullSubcategoryCongr
    (by ext; apply isIndObject_iff_preservesFiniteLimits)

Depends on / 依赖: Ind.equivalence, ObjectProperty, ObjectProperty.fullSubcategoryCongr, equivalence, fullSubcategoryCongr, isIndObject_iff_preservesFiniteLimits
-/
noncomputable def Ind.leftExactFunctorEquivalence : Ind C ≌ LeftExactFunctor Cᵒᵖ (Type u) :=
(Ind.equivalence _).trans ObjectProperty.fullSubcategoryCongr
    (by ext; apply isIndObject_iff_preservesFiniteLimits)

end Small

end CategoryTheory
