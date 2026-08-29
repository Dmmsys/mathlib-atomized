/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.Data.Countable.Small

/-!
# Countable categories

A category is countable in this sense if it has countably many objects and countably many morphisms.

-/

@[expose] public section

universe w v u

noncomputable section

namespace CategoryTheory

/--
Instance `discreteCountable` / 实例 `discreteCountable`

English:
instance discreteCountable
  signature: {α : Type*} [Countable α]
  body: Countable.of_equiv α discreteEquiv.symm

中文:
实例 discreteCountable
  签名: {α : 类型} [Countable α]
  定义体: Countable.of_equiv α discreteEquiv.symm

Depends on / 依赖: Countable, Countable.of_equiv, discreteEquiv, discreteEquiv.symm, of_equiv
-/
instance discreteCountable {α : Type*} [Countable α] : Countable (Discrete α) :=
  Countable.of_equiv α discreteEquiv.symm

/--
Definition of `CountableCategory` / `CountableCategory` 的定义

English:
class CountableCategory
  parameters: (J : Type*) [Category* J]
  axioms and operations (2):
    - countableObj : Countable J  [default: by infer_instance]
    - countableHom : forall j j' : J, Countable (j ⟶ j')  [default: by infer_instance]

中文:
类 CountableCategory
  参数: (J : 类型) [Category* J]
  公理与运算 (2 个):
    - countableObj : Countable J  [默认: by infer_instance]
    - countableHom : 对任意 j j' : J, Countable (j ⟶ j')  [默认: by infer_instance]

Depends on / 依赖: Countable, countableHom, infer_instance
-/
class CountableCategory (J : Type*) [Category* J] : Prop where
  countableObj : Countable J := by infer_instance
  countableHom : forall j j' : J, Countable (j ⟶ j') := by infer_instance

attribute [instance] CountableCategory.countableObj CountableCategory.countableHom

/--
Instance `countableCategoryDiscreteOfCountable` / 实例 `countableCategoryDiscreteOfCountable`

English:
instance countableCategoryDiscreteOfCountable
  signature: (J : Type*) [Countable J]

中文:
实例 countableCategoryDiscreteOfCountable
  签名: (J : 类型) [Countable J]
-/
instance countableCategoryDiscreteOfCountable (J : Type*) [Countable J] :
    CountableCategory (Discrete J) where

instance {J : Type u} [Countable J] [Category* J] [Quiver.IsThin J] : CountableCategory J :=
  CountableCategory.mk inferInstance (fun _ _ => ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CountableCategory Nat

中文:
实例 :
  签名: CountableCategory 自然数
-/
instance : CountableCategory Nat where

namespace CountableCategory

variable (α : Type u) [Category.{v} α] [CountableCategory α]

/--
Definition of `ObjAsType` / `ObjAsType` 的定义

English:
abbreviation ObjAsType
  signature: : Type
  body: InducedCategory α (equivShrink.{0} α).symm

中文:
缩写 ObjAsType
  签名: : Type
  定义体: InducedCategory α (equivShrink.{0} α).symm

Depends on / 依赖: InducedCategory, equivShrink
-/
abbrev ObjAsType : Type :=
  InducedCategory α (equivShrink.{0} α).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Countable (ObjAsType α)
  body: Countable.of_equiv α (equivShrink.{0} α)

中文:
实例 :
  签名: Countable (ObjAsType α)
  定义体: Countable.of_equiv α (equivShrink.{0} α)

Depends on / 依赖: Countable, Countable.of_equiv, equivShrink, of_equiv
-/
instance : Countable (ObjAsType α) := Countable.of_equiv α (equivShrink.{0} α)

instance {i j : ObjAsType α} : Countable (i ⟶ j) :=
  Countable.of_equiv _ InducedCategory.homEquiv.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CountableCategory (ObjAsType α)

中文:
实例 :
  签名: CountableCategory (ObjAsType α)
-/
instance : CountableCategory (ObjAsType α) where

/--
Definition of `objAsTypeEquiv` / `objAsTypeEquiv` 的定义

English:
definition objAsTypeEquiv
  signature: : ObjAsType α ≌ α
  body: (inducedFunctor (equivShrink.{0} α).symm).asEquivalence

中文:
定义 objAsTypeEquiv
  签名: : ObjAsType α ≌ α
  定义体: (inducedFunctor (equivShrink.{0} α).symm).asEquivalence

Depends on / 依赖: asEquivalence, equivShrink, inducedFunctor
-/
noncomputable def objAsTypeEquiv : ObjAsType α ≌ α :=
  (inducedFunctor (equivShrink.{0} α).symm).asEquivalence

/--
Definition of `HomAsType` / `HomAsType` 的定义

English:
definition HomAsType
  body: ShrinkHoms (ObjAsType α)

中文:
定义 HomAsType
  定义体: ShrinkHoms (ObjAsType α)

Depends on / 依赖: ObjAsType, ShrinkHoms
-/
def HomAsType := ShrinkHoms (ObjAsType α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LocallySmall.{0} (ObjAsType α)
  body: inferInstance

中文:
实例 :
  签名: LocallySmall.{0} (ObjAsType α)
  定义体: inferInstance
-/
instance : LocallySmall.{0} (ObjAsType α) where
  hom_small _ _ := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SmallCategory (HomAsType α)
  body: inferInstanceAs SmallCategory (ShrinkHoms _)

中文:
实例 :
  签名: SmallCategory (HomAsType α)
  定义体: inferInstanceAs SmallCategory (ShrinkHoms _)

Depends on / 依赖: ShrinkHoms, SmallCategory
-/
instance : SmallCategory (HomAsType α) := inferInstanceAs SmallCategory (ShrinkHoms _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Countable (HomAsType α)
  body: Countable.of_equiv α (equivShrink.{0} α)

中文:
实例 :
  签名: Countable (HomAsType α)
  定义体: Countable.of_equiv α (equivShrink.{0} α)

Depends on / 依赖: Countable, Countable.of_equiv, equivShrink, of_equiv
-/
instance : Countable (HomAsType α) := Countable.of_equiv α (equivShrink.{0} α)

instance {i j : HomAsType α} : Countable (i ⟶ j) :=
  Countable.of_equiv ((ShrinkHoms.equivalence _).inverse.obj i ⟶
    (ShrinkHoms.equivalence _).inverse.obj j)
    (Functor.FullyFaithful.ofFullyFaithful _).homEquiv.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CountableCategory (HomAsType α)

中文:
实例 :
  签名: CountableCategory (HomAsType α)
-/
instance : CountableCategory (HomAsType α) where

/--
Definition of `homAsTypeEquiv` / `homAsTypeEquiv` 的定义

English:
definition homAsTypeEquiv
  signature: : HomAsType α ≌ α
  body: (ShrinkHoms.equivalence _).symm.trans (objAsTypeEquiv _)

中文:
定义 homAsTypeEquiv
  签名: : HomAsType α ≌ α
  定义体: (ShrinkHoms.equivalence _).symm.trans (objAsTypeEquiv _)

Depends on / 依赖: ShrinkHoms, ShrinkHoms.equivalence, equivalence, objAsTypeEquiv, symm.trans
-/
noncomputable def homAsTypeEquiv : HomAsType α ≌ α :=
  (ShrinkHoms.equivalence _).symm.trans (objAsTypeEquiv _)

end CountableCategory

instance (α : Type*) [SmallCategory α] [FinCategory α] : CountableCategory α where

open Opposite

/--
Instance `countableCategoryOpposite` / 实例 `countableCategoryOpposite`

English:
instance countableCategoryOpposite
  signature: {J : Type*} [Category* J] [CountableCategory J]
  body: Countable.of_equiv _ equivToOpposite
  countableHom j j' := Countable.of_equiv _ (opEquiv j j').symm

中文:
实例 countableCategoryOpposite
  签名: {J : 类型} [Category* J] [CountableCategory J]
  定义体: Countable.of_equiv _ equivToOpposite
  countableHom j j' := Countable.of_equiv _ (opEquiv j j').symm

Depends on / 依赖: Countable, Countable.of_equiv, equivToOpposite, of_equiv
-/
instance countableCategoryOpposite {J : Type*} [Category* J] [CountableCategory J] :
    CountableCategory Jᵒᵖ where
  countableObj := Countable.of_equiv _ equivToOpposite
  countableHom j j' := Countable.of_equiv _ (opEquiv j j').symm

attribute [local instance] uliftCategory in
/--
Instance `countableCategoryUlift` / 实例 `countableCategoryUlift`

English:
instance countableCategoryUlift
  signature: {J : Type v} [Category.{v} J] [CountableCategory J]
  body: instCountableULift
  countableHom := fun i j =>
    have : Countable ((ULiftHom.objDown i).down ⟶ (ULiftHom.objDown j).down) := inferInstance
    instCountableULift

中文:
实例 countableCategoryUlift
  签名: {J : 类型v} [Category.{v} J] [CountableCategory J]
  定义体: instCountableULift
  countableHom := fun i j =>
    have : Countable ((ULiftHom.objDown i).down ⟶ (ULiftHom.objDown j).down) := inferInstance
    instCountableULift

Depends on / 依赖: instCountableULift
-/
instance countableCategoryUlift {J : Type v} [Category.{v} J] [CountableCategory J] :
    CountableCategory.{max w v} (ULiftHom.{w, max w v} (ULift.{w, v} J)) where
  countableObj := instCountableULift
  countableHom := fun i j =>
    have : Countable ((ULiftHom.objDown i).down ⟶ (ULiftHom.objDown j).down) := inferInstance
    instCountableULift

end CategoryTheory
