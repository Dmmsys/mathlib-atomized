/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Bicategory.End
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Promoting a monoidal category to a single object bicategory.

A monoidal category can be thought of as a bicategory with a single object.

The objects of the monoidal category become the 1-morphisms,
with composition given by tensor product,
and the morphisms of the monoidal category become the 2-morphisms.

We verify that the endomorphisms of that single object recovers the original monoidal category.

One could go much further: the bicategory of monoidal categories
(equipped with monoidal functors and monoidal natural transformations)
is equivalent to the bicategory consisting of
* single object bicategories,
* pseudofunctors, and
* (oplax) natural transformations `η` such that `η.app Unit.unit = 𝟙 _`.
-/

@[expose] public section

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- Promote a monoidal category to a bicategory with a single object.
(The objects of the monoidal category become the 1-morphisms,
with composition given by tensor product,
and the morphisms of the monoidal category become the 2-morphisms.)
-/
@[nolint unusedArguments]
/--
Definition of `MonoidalSingleObj` / `MonoidalSingleObj` 的定义

English:
definition MonoidalSingleObj
  signature: (C : Type u) [Category.{v} C] [MonoidalCategory C]
  body: Unit
deriving Inhabited

中文:
定义 MonoidalSingleObj
  签名: (C : 类型u) [Category.{v} C] [MonoidalCategory C]
  定义体: Unit
deriving Inhabited
-/
def MonoidalSingleObj (C : Type u) [Category.{v} C] [MonoidalCategory C] :=
  Unit
deriving Inhabited

open MonoidalCategory

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bicategory (MonoidalSingleObj C)
  body: C
  id _ := 𝟙_ C
  comp X Y := tensorObj X Y
  whiskerLeft X _ _ f := X ◁ f
  whiskerRight f Z := f ▷ Z
  associator X Y Z := α_ X Y Z
  leftUnitor X := fun_ X
  rightUnitor X := ρ_ X
  whisker_exchange := whisker_exchange

中文:
实例 :
  签名: Bicategory (MonoidalSingleObj C)
  定义体: C
  id _ := 𝟙_ C
  comp X Y := tensorObj X Y
  whiskerLeft X _ _ f := X ◁ f
  whiskerRight f Z := f ▷ Z
  associator X Y Z := α_ X Y Z
  leftUnitor X := fun_ X
  rightUnitor X := ρ_ X
  whisker_exchange := whisker_exchange
-/
instance : Bicategory (MonoidalSingleObj C) where
  Hom _ _ := C
  id _ := 𝟙_ C
  comp X Y := tensorObj X Y
  whiskerLeft X _ _ f := X ◁ f
  whiskerRight f Z := f ▷ Z
  associator X Y Z := α_ X Y Z
  leftUnitor X := fun_ X
  rightUnitor X := ρ_ X
  whisker_exchange := whisker_exchange

namespace MonoidalSingleObj

/-- The unique object in the bicategory obtained by "promoting" a monoidal category. -/
@[nolint unusedArguments]
/--
Definition of `star` / `star` 的定义

English:
definition star
  signature: : MonoidalSingleObj C
  body: Unit.unit

中文:
定义 star
  签名: : MonoidalSingleObj C
  定义体: Unit.unit
-/
protected def star : MonoidalSingleObj C :=
  Unit.unit

/-- The monoidal functor from the endomorphisms of the single object
when we promote a monoidal category to a single object bicategory,
to the original monoidal category.

We subsequently show this is an equivalence.
-/
@[simps]
/--
Definition of `endMonoidalStarFunctor` / `endMonoidalStarFunctor` 的定义

English:
definition endMonoidalStarFunctor
  signature: : (EndMonoidal (MonoidalSingleObj.star C)) ⥤ C where
  body: X
  map f := f

中文:
定义 endMonoidalStarFunctor
  签名: : (EndMonoidal (MonoidalSingleObj.star C)) ⥤ C where
  定义体: X
  map f := f
-/
def endMonoidalStarFunctor : (EndMonoidal (MonoidalSingleObj.star C)) ⥤ C where
  obj X := X
  map f := f

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (endMonoidalStarFunctor C).Monoidal
  body: Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

中文:
实例 :
  签名: (endMonoidalStarFunctor C).Monoidal
  定义体: Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

Depends on / 依赖: CoreMonoidal, Functor, Functor.CoreMonoidal.toMonoidal, Iso.refl, toMonoidal
-/
instance : (endMonoidalStarFunctor C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

set_option backward.defeqAttrib.useBackward true in
/-- The equivalence between the endomorphisms of the single object
when we promote a monoidal category to a single object bicategory,
and the original monoidal category.
-/
@[simps]
/--
Definition of `endMonoidalStarFunctorEquivalence` / `endMonoidalStarFunctorEquivalence` 的定义

English:
definition endMonoidalStarFunctorEquivalence
  signature: :
  body: endMonoidalStarFunctor C
  inverse :=
    { obj := fun X => X
      map := fun f => f }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 endMonoidalStarFunctorEquivalence
  签名: :
  定义体: endMonoidalStarFunctor C
  inverse :=
    { obj := fun X => X
      map := fun f => f }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: endMonoidalStarFunctor
-/
noncomputable def endMonoidalStarFunctorEquivalence :
    EndMonoidal (MonoidalSingleObj.star C) ≌ C where
  functor := endMonoidalStarFunctor C
  inverse :=
    { obj := fun X => X
      map := fun f => f }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/--
Instance `endMonoidalStarFunctor_isEquivalence` / 实例 `endMonoidalStarFunctor_isEquivalence`

English:
instance endMonoidalStarFunctor_isEquivalence
  signature: : (endMonoidalStarFunctor C).IsEquivalence
  body: (endMonoidalStarFunctorEquivalence C).isEquivalence_functor

中文:
实例 endMonoidalStarFunctor_isEquivalence
  签名: : (endMonoidalStarFunctor C).IsEquivalence
  定义体: (endMonoidalStarFunctorEquivalence C).isEquivalence_functor

Depends on / 依赖: endMonoidalStarFunctorEquivalence, isEquivalence_functor
-/
instance endMonoidalStarFunctor_isEquivalence : (endMonoidalStarFunctor C).IsEquivalence :=
  (endMonoidalStarFunctorEquivalence C).isEquivalence_functor

end MonoidalSingleObj

end CategoryTheory
