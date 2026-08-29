/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# Cartesian closure of Type

Show that `Type u₁` is Cartesian closed, and `C ⥤ Type u₁` is Cartesian closed for `C` a small
category in `Type u₁`.
Note this implies that the category of presheaves on a small category `C` is Cartesian closed.
-/

@[expose] public section


namespace CategoryTheory

noncomputable section

open Category Limits MonoidalCategory

universe v₁ v₂ u₁ u₂

variable {C : Type v₂} [Category.{v₁} C]

section MonoidalClosed

/--
Definition of `Types.tensorProductAdjunction` / `Types.tensorProductAdjunction` 的定义

English:
definition Types.tensorProductAdjunction
  signature: (X : Type v₁)
  body: { app Z := ↾fun z => ↾fun x => ⟨x, z⟩ }
  counit := { app _ := ↾fun xf => xf.2.hom xf.1 }

中文:
定义 Types.tensorProductAdjunction
  签名: (X : 类型v₁)
  定义体: { app Z := ↾fun z => ↾fun x => ⟨x, z⟩ }
  counit := { app _ := ↾fun xf => xf.2.hom xf.1 }
-/
def Types.tensorProductAdjunction (X : Type v₁) :
    tensorLeft X ⊣ coyoneda.obj (Opposite.op X) where
  unit := { app Z := ↾fun z => ↾fun x => ⟨x, z⟩ }
  counit := { app _ := ↾fun xf => xf.2.hom xf.1 }

instance (X : Type v₁) : (tensorLeft X).IsLeftAdjoint :=
  ⟨_, ⟨Types.tensorProductAdjunction X⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalClosed (Type v₁)
  body: MonoidalClosed.mk
  fun X => Closed.mk _ (Types.tensorProductAdjunction X)

中文:
实例 :
  签名: 幺半群闭 (类型v₁)
  定义体: MonoidalClosed.mk
  fun X => Closed.mk _ (Types.tensorProductAdjunction X)

Depends on / 依赖: MonoidalClosed, MonoidalClosed.mk
-/
instance : MonoidalClosed (Type v₁) := MonoidalClosed.mk
  fun X => Closed.mk _ (Types.tensorProductAdjunction X)

instance {C : Type v₁} [SmallCategory C] : MonoidalClosed (C ⥤ Type v₁) :=
  MonoidalClosed.mk fun F => by
    haveI : forall X : Type v₁, PreservesColimits (tensorLeft X) := by infer_instance
    letI : PreservesColimits (tensorLeft F) := ⟨by infer_instance⟩
    have := Presheaf.isLeftAdjoint_of_preservesColimits.{v₁} (tensorLeft F)
    exact Closed.mk _ (Adjunction.ofIsLeftAdjoint (tensorLeft F))

-- TODO: once we have `MonoidalClosed` instances for functor categories into general monoidal
-- closed categories, replace this with that, as it will be a more explicit construction.
attribute [local instance] uliftCategory in
/-- This is not a good instance because of the universe levels. Below is the instance where the
target category is `Type (max u₁ v₁)`. -/
@[instance_reducible]
/--
Definition of `cartesianClosedFunctorToTypes` / `cartesianClosedFunctorToTypes` 的定义

English:
definition cartesianClosedFunctorToTypes
  signature: {C : Type u₁} [Category.{v₁} C]
  body: let e : (ULiftHom.{max u₁ v₁ u₂} (ULift.{max u₁ v₁ u₂} C)) ⥤ Type (max u₁ v₁ u₂) ≌
      C ⥤ Type (max u₁ v₁ u₂) :=
      Functor.asEquivalence ((Functor.whiskeringLeft _ _ _).obj
        (ULift.equivalence.trans ULiftHom.equiv).functor)
  cartesianClosedOfEquiv e

中文:
定义 cartesianClosedFunctorToTypes
  签名: {C : 类型u₁} [范畴.{v₁} C]
  定义体: let e : (ULiftHom.{max u₁ v₁ u₂} (ULift.{max u₁ v₁ u₂} C)) ⥤ Type (max u₁ v₁ u₂) ≌
      C ⥤ Type (max u₁ v₁ u₂) :=
      Functor.asEquivalence ((Functor.whiskeringLeft _ _ _).obj
        (ULift.equivalence.trans ULiftHom.equiv).functor)
  cartesianClosedOfEquiv e

Depends on / 依赖: Functor, Functor.asEquivalence, Functor.whiskeringLeft, ULift.equivalence.trans, ULiftHom, ULiftHom.equiv, asEquivalence, cartesianClosedOfEquiv, equivalence, functor, whiskeringLeft
-/
def cartesianClosedFunctorToTypes {C : Type u₁} [Category.{v₁} C] :
    MonoidalClosed (C ⥤ Type (max u₁ v₁ u₂)) :=
  let e : (ULiftHom.{max u₁ v₁ u₂} (ULift.{max u₁ v₁ u₂} C)) ⥤ Type (max u₁ v₁ u₂) ≌
      C ⥤ Type (max u₁ v₁ u₂) :=
      Functor.asEquivalence ((Functor.whiskeringLeft _ _ _).obj
        (ULift.equivalence.trans ULiftHom.equiv).functor)
  cartesianClosedOfEquiv e

-- TODO: once we have `MonoidalClosed` instances for functor categories into general monoidal
-- closed categories, replace this with that, as it will be a more explicit construction.
instance {C : Type u₁} [Category.{v₁} C] : MonoidalClosed (C ⥤ Type (max u₁ v₁)) :=
  cartesianClosedFunctorToTypes

-- TODO: once we have `MonoidalClosed` instances for functor categories into general monoidal
-- closed categories, replace this with that, as it will be a more explicit construction.
instance {C : Type u₁} [Category.{v₁} C] [EssentiallySmall.{v₁} C] :
    MonoidalClosed (C ⥤ Type v₁) :=
  let e : (SmallModel C) ⥤ Type v₁ ≌ C ⥤ Type v₁ :=
    Functor.asEquivalence ((Functor.whiskeringLeft _ _ _).obj (equivSmallModel _).functor)
  cartesianClosedOfEquiv e

end MonoidalClosed

end

end CategoryTheory
