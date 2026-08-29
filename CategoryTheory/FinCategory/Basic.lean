/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Category.ULift

/-!
# Finite categories

A category is finite in this sense if it has finitely many objects, and finitely many morphisms.

## Implementation
Prior to https://github.com/leanprover-community/mathlib4/pull/14046, `FinCategory` required a `DecidableEq` instance on the object and morphism types.
This does not seem to have had any practical payoff (i.e. making some definition constructive)
so we have removed these requirements to avoid
having to supply instances or delay with non-defeq conflicts between instances.
-/

public section


universe w v u

noncomputable section

namespace CategoryTheory

/--
Instance `discreteFintype` / 实例 `discreteFintype`

English:
instance discreteFintype
  signature: {α : Type*} [Fintype α]
  body: Fintype.ofEquiv α discreteEquiv.symm

中文:
实例 discreteFintype
  签名: {α : 类型} [Fintype α]
  定义体: Fintype.ofEquiv α discreteEquiv.symm

Depends on / 依赖: Fintype, Fintype.ofEquiv, discreteEquiv, discreteEquiv.symm, ofEquiv
-/
instance discreteFintype {α : Type*} [Fintype α] : Fintype (Discrete α) :=
  Fintype.ofEquiv α discreteEquiv.symm

instance {α : Type*} [Finite α] : Finite (Discrete α) :=
  Finite.of_equiv α discreteEquiv.symm

/--
Instance `discreteHomFintype` / 实例 `discreteHomFintype`

English:
instance discreteHomFintype
  signature: {α : Type*} (X Y : Discrete α)
  body: by
  classical
  apply ULift.fintype

中文:
实例 discreteHomFintype
  签名: {α : 类型} (X Y : Discrete α)
  定义体: by
  classical
  apply ULift.fintype

Depends on / 依赖: ULift.fintype, classical, fintype
-/
instance discreteHomFintype {α : Type*} (X Y : Discrete α) : Fintype (X ⟶ Y) := by
  classical
  apply ULift.fintype

/--
Definition of `FinCategory` / `FinCategory` 的定义

English:
class FinCategory
  parameters: (J : Type v) [SmallCategory J]
  axioms and operations (2):
    - fintypeObj : Fintype J  [default: by infer_instance]
    - fintypeHom : forall j j' : J, Fintype (j ⟶ j')  [default: by infer_instance]

中文:
类 FinCategory
  参数: (J : 类型v) [SmallCategory J]
  公理与运算 (2 个):
    - fintypeObj : Fintype J  [默认: by infer_instance]
    - fintypeHom : 对任意 j j' : J, Fintype (j ⟶ j')  [默认: by infer_instance]

Depends on / 依赖: Fintype, fintypeHom, infer_instance
-/
class FinCategory (J : Type v) [SmallCategory J] where
  fintypeObj : Fintype J := by infer_instance
  fintypeHom : forall j j' : J, Fintype (j ⟶ j') := by infer_instance

attribute [instance_reducible, instance] FinCategory.fintypeObj FinCategory.fintypeHom

/--
Instance `finCategoryDiscreteOfFintype` / 实例 `finCategoryDiscreteOfFintype`

English:
instance finCategoryDiscreteOfFintype
  signature: (J : Type v) [Fintype J]

中文:
实例 finCategoryDiscreteOfFintype
  签名: (J : 类型v) [Fintype J]
-/
instance finCategoryDiscreteOfFintype (J : Type v) [Fintype J] : FinCategory (Discrete J) where

instance {J : Type u} [Fintype J] [SmallCategory J] [Quiver.IsThin J] : FinCategory J :=
  FinCategory.mk ‹Fintype J› fun j j' => Fintype.ofFinite (j ⟶ j')

open Opposite

/--
Instance `finCategoryOpposite` / 实例 `finCategoryOpposite`

English:
instance finCategoryOpposite
  signature: {J : Type v} [SmallCategory J] [FinCategory J]
  body: Fintype.ofEquiv _ equivToOpposite
  fintypeHom j j' := Fintype.ofEquiv _ (opEquiv j j').symm

中文:
实例 finCategoryOpposite
  签名: {J : 类型v} [SmallCategory J] [FinCategory J]
  定义体: Fintype.ofEquiv _ equivToOpposite
  fintypeHom j j' := Fintype.ofEquiv _ (opEquiv j j').symm

Depends on / 依赖: Fintype, Fintype.ofEquiv, equivToOpposite, ofEquiv
-/
instance finCategoryOpposite {J : Type v} [SmallCategory J] [FinCategory J] : FinCategory Jᵒᵖ where
  fintypeObj := Fintype.ofEquiv _ equivToOpposite
  fintypeHom j j' := Fintype.ofEquiv _ (opEquiv j j').symm

attribute [local instance] uliftCategory in
/--
Instance `finCategoryUlift` / 实例 `finCategoryUlift`

English:
instance finCategoryUlift
  signature: {J : Type v} [SmallCategory J] [FinCategory J]
  body: ULift.fintype J
  fintypeHom := fun _ _ => ULift.fintype _

中文:
实例 finCategoryUlift
  签名: {J : 类型v} [SmallCategory J] [FinCategory J]
  定义体: ULift.fintype J
  fintypeHom := fun _ _ => ULift.fintype _

Depends on / 依赖: ULift.fintype, fintype
-/
instance finCategoryUlift {J : Type v} [SmallCategory J] [FinCategory J] :
    FinCategory.{max w v} (ULiftHom.{w, max w v} (ULift.{w, v} J)) where
  fintypeObj := ULift.fintype J
  fintypeHom := fun _ _ => ULift.fintype _

end CategoryTheory
