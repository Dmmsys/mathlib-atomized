/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.WithTerminal.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# The Augmented simplex category

This file defines the `AugmentedSimplexCategory` as the category obtained by adding an initial
object to `SimplexCategory` (using `CategoryTheory.WithInitial`).

This definition provides a canonical full and faithful inclusion functor
`inclusion : SimplexCategory ⥤ AugmentedSimplexCategory`.

We prove that functors out of `AugmentedSimplexCategory` are equivalent to augmented cosimplicial
objects and that functors out of `AugmentedSimplexCategoryᵒᵖ` are equivalent to augmented simplicial
objects, and we provide a translation of the main constructions on augmented (co)simplicial objects
(i.e `drop`, `point` and `toArrow`) in terms of these equivalences.

-/

@[expose] public section

open CategoryTheory

/--
Definition of `AugmentedSimplexCategory` / `AugmentedSimplexCategory` 的定义

English:
abbreviation AugmentedSimplexCategory
  body: WithInitial SimplexCategory

中文:
缩写 AugmentedSimplexCategory
  定义体: WithInitial SimplexCategory

Depends on / 依赖: SimplexCategory, WithInitial
-/
abbrev AugmentedSimplexCategory := WithInitial SimplexCategory

namespace AugmentedSimplexCategory

variable {C : Type*} [Category* C]

/-- The canonical inclusion from `SimplexCategory` to `AugmentedSimplexCategory`. -/
@[simps!]
/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: : SimplexCategory ⥤ AugmentedSimplexCategory
  body: WithInitial.incl

中文:
定义 inclusion
  签名: : 单纯形范畴 ⥤ AugmentedSimplexCategory
  定义体: WithInitial.incl

Depends on / 依赖: WithInitial, WithInitial.incl
-/
def inclusion : SimplexCategory ⥤ AugmentedSimplexCategory := WithInitial.incl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: inclusion.Full
  body: inferInstanceAs WithInitial.incl.Full

中文:
实例 :
  签名: inclusion.满
  定义体: inferInstanceAs WithInitial.incl.Full

Depends on / 依赖: WithInitial, WithInitial.incl.Full
-/
instance : inclusion.Full := inferInstanceAs WithInitial.incl.Full
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: inclusion.Faithful
  body: inferInstanceAs WithInitial.incl.Faithful

中文:
实例 :
  签名: inclusion.忠实
  定义体: inferInstanceAs WithInitial.incl.Faithful

Depends on / 依赖: Faithful, WithInitial, WithInitial.incl.Faithful
-/
instance : inclusion.Faithful := inferInstanceAs WithInitial.incl.Faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Limits.HasInitial AugmentedSimplexCategory
  body: inferInstanceAs Limits.HasInitial WithInitial _

中文:
实例 :
  签名: Limits.HasInitial AugmentedSimplexCategory
  定义体: inferInstanceAs Limits.HasInitial WithInitial _

Depends on / 依赖: HasInitial, Limits, Limits.HasInitial, WithInitial
-/
instance : Limits.HasInitial AugmentedSimplexCategory :=
inferInstanceAs Limits.HasInitial WithInitial _

/-- The equivalence between functors out of `AugmentedSimplexCategory` and augmented
cosimplicial objects. -/
@[simps!]
/--
Definition of `equivAugmentedCosimplicialObject` / `equivAugmentedCosimplicialObject` 的定义

English:
definition equivAugmentedCosimplicialObject
  signature: :
  body: WithInitial.equivComma

#adaptation_note

中文:
定义 equivAugmentedCosimplicialObject
  签名: :
  定义体: WithInitial.equivComma

#adaptation_note

Depends on / 依赖: WithInitial, WithInitial.equivComma, equivComma
-/
def equivAugmentedCosimplicialObject :
    (AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Augmented C :=
  WithInitial.equivComma

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Through the equivalence `(AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Augmented C`,
dropping the augmentation corresponds to precomposition with
`inclusion : SimplexCategory ⥤ AugmentedSimplexCategory`. -/
@[simps!]
/--
Definition of `equivAugmentedCosimplicialObjectFunctorCompDropIso` / `equivAugmentedCosimplicialObjectFunctorCompDropIso` 的定义

English:
definition equivAugmentedCosimplicialObjectFunctorCompDropIso
  signature: :
  body: .refl _

#adaptation_note

中文:
定义 equivAugmentedCosimplicialObjectFunctorCompDropIso
  签名: :
  定义体: .refl _

#adaptation_note
-/
def equivAugmentedCosimplicialObjectFunctorCompDropIso :
    equivAugmentedCosimplicialObject.functor ⋙ CosimplicialObject.Augmented.drop ≅
    (Functor.whiskeringLeft _ _ C).obj inclusion :=
  .refl _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Through the equivalence `(AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Augmented C`,
taking the point of the augmentation corresponds to evaluation at the initial object. -/
@[simps!]
/--
Definition of `equivAugmentedCosimplicialObjectFunctorCompPointIso` / `equivAugmentedCosimplicialObjectFunctorCompPointIso` 的定义

English:
definition equivAugmentedCosimplicialObjectFunctorCompPointIso
  signature: :
  body: .refl _

中文:
定义 equivAugmentedCosimplicialObjectFunctorCompPointIso
  签名: :
  定义体: .refl _
-/
def equivAugmentedCosimplicialObjectFunctorCompPointIso :
    equivAugmentedCosimplicialObject.functor ⋙ CosimplicialObject.Augmented.point ≅
    ((evaluation _ _).obj .star : (AugmentedSimplexCategory ⥤ C) ⥤ C) :=
  .refl _

/-- Through the equivalence `(AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Augmented C`,
the arrow attached to the cosimplicial object is the one obtained by evaluation at the unique arrow
`star ⟶ of [0]`. -/
@[simps!]
/--
Definition of `equivAugmentedCosimplicialObjectFunctorCompToArrowIso` / `equivAugmentedCosimplicialObjectFunctorCompToArrowIso` 的定义

English:
definition equivAugmentedCosimplicialObjectFunctorCompToArrowIso
  signature: :
  body: .refl _

#adaptation_note

中文:
定义 equivAugmentedCosimplicialObjectFunctorCompToArrowIso
  签名: :
  定义体: .refl _

#adaptation_note
-/
def equivAugmentedCosimplicialObjectFunctorCompToArrowIso :
    equivAugmentedCosimplicialObject.functor ⋙ CosimplicialObject.Augmented.toArrow ≅
    Functor.mapArrowFunctor _ C ⋙
      (evaluation _ _ |>.obj <| .mk <| WithInitial.homTo <| .mk 0) :=
  .refl _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The equivalence between functors out of `AugmentedSimplexCategory` and augmented simplicial
objects. -/
@[simps!]
/--
Definition of `equivAugmentedSimplicialObject` / `equivAugmentedSimplicialObject` 的定义

English:
definition equivAugmentedSimplicialObject
  signature: :
  body: .trans WithTerminal.equivComma .congrLeft WithInitial.opEquiv SimplexCategory

中文:
定义 equivAugmentedSimplicialObject
  签名: :
  定义体: .trans WithTerminal.equivComma .congrLeft WithInitial.opEquiv SimplexCategory

Depends on / 依赖: SimplexCategory, WithInitial, WithInitial.opEquiv, WithTerminal, WithTerminal.equivComma, congrLeft, equivComma, opEquiv
-/
def equivAugmentedSimplicialObject :
    (AugmentedSimplexCategoryᵒᵖ ⥤ C) ≌ SimplicialObject.Augmented C :=
.trans WithTerminal.equivComma .congrLeft WithInitial.opEquiv SimplexCategory

/-- Through the equivalence `(AugmentedSimplexCategoryᵒᵖ ⥤ C) ≌ SimplicialObject.Augmented C`,
dropping the augmentation corresponds to precomposition with
`inclusionᵒᵖ : SimplexCategoryᵒᵖ ⥤ AugmentedSimplexCategoryᵒᵖ`. -/
@[simps!]
/--
Definition of `equivAugmentedSimplicialObjectFunctorCompDropIso` / `equivAugmentedSimplicialObjectFunctorCompDropIso` 的定义

English:
definition equivAugmentedSimplicialObjectFunctorCompDropIso
  signature: :
  body: .refl _

中文:
定义 equivAugmentedSimplicialObjectFunctorCompDropIso
  签名: :
  定义体: .refl _
-/
def equivAugmentedSimplicialObjectFunctorCompDropIso :
    equivAugmentedSimplicialObject.functor ⋙ SimplicialObject.Augmented.drop ≅
    (Functor.whiskeringLeft _ _ C).obj inclusion.op :=
  .refl _

/-- Through the equivalence `(AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Augmented C`,
taking the point of the augmentation corresponds to evaluation at the initial object. -/
@[simps!]
/--
Definition of `equivAugmentedSimplicialObjectFunctorCompPointIso` / `equivAugmentedSimplicialObjectFunctorCompPointIso` 的定义

English:
definition equivAugmentedSimplicialObjectFunctorCompPointIso
  signature: :
  body: .refl _

中文:
定义 equivAugmentedSimplicialObjectFunctorCompPointIso
  签名: :
  定义体: .refl _
-/
def equivAugmentedSimplicialObjectFunctorCompPointIso :
    equivAugmentedSimplicialObject.functor ⋙ SimplicialObject.Augmented.point ≅
    (evaluation _ C).obj (.op .star) :=
  .refl _

/-- Through the equivalence `(AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Augmented C`,
the arrow attached to the cosimplicial object is the one obtained by evaluation at the unique arrow
`star ⟶ of [0]`. -/
@[simps!]
/--
Definition of `equivAugmentedSimplicialObjectFunctorCompToArrowIso` / `equivAugmentedSimplicialObjectFunctorCompToArrowIso` 的定义

English:
definition equivAugmentedSimplicialObjectFunctorCompToArrowIso
  signature: :
  body: .refl _

中文:
定义 equivAugmentedSimplicialObjectFunctorCompToArrowIso
  签名: :
  定义体: .refl _
-/
def equivAugmentedSimplicialObjectFunctorCompToArrowIso :
    equivAugmentedSimplicialObject.functor ⋙ SimplicialObject.Augmented.toArrow ≅
    Functor.mapArrowFunctor _ C ⋙
      (evaluation _ _ |>.obj <| .mk <| .op <| WithInitial.homTo <| .mk 0) :=
  .refl _

end AugmentedSimplexCategory
