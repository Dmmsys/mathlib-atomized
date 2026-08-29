/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Dagur Asgeirsson, Emily Riehl
-/
module

public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Existence of conical limits

This file contains different statements about the (non-constructive) existence of conical limits.

The main constructions are the following.

- `HasConicalLimit`: there exists a conical limit for `F : J ⥤ C`.
- `HasConicalLimitsOfShape J`: All functors `F : J ⥤ C` have conical limits.
- `HasConicalLimitsOfSize.{v₁, u₁}`: For all small `J` all functors `F : J ⥤ C` have conical limits.
- `HasConicalLimits`: `C` has all (small) conical limits.

## References

* [Kelly G.M., *Basic concepts of enriched category theory*][kelly2005]:
  See section 3.8 for a similar treatment, although the content of this file is not directly
  adapted from there.

## Implementation notes

`V` has been made an `(V : outParam <| Type u')` in the classes below as it seems instance
inference prefers this. Otherwise it failed with
`cannot find synthesization order` on the instances below.
However, it is not fully clear yet whether this could lead to potential issues, for example
if there are multiple `MonoidalCategory _` instances in scope.
-/

public section

universe v₁ u₁ v₂ u₂ w v' v u u'

namespace CategoryTheory.Enriched

open Limits

section Definitions

variable {J : Type u₁} [Category.{v₁} J]
variable (V : outParam <| Type u') [Category.{v'} V] [MonoidalCategory V]
variable (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C]

variable {C} in
/--
Definition of `HasConicalLimit` / `HasConicalLimit` 的定义

English:
class HasConicalLimit
  parameters: (F : J ⥤ C)
  extends: HasLimit F
  axioms and operations (1):
    - preservesLimit_eCoyoneda((X : C)) : PreservesLimit F (eCoyoneda V X)  [default: by infer_instance]

中文:
类 有余nicalLimit
  参数: (F : J ⥤ C)
  继承: 有极限 F
  公理与运算 (1 个):
    - preservesLimit_eCoyoneda((X : C)) : 保持极限 F (eCoyoneda V X)  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class HasConicalLimit (F : J ⥤ C) : Prop extends HasLimit F where
  preservesLimit_eCoyoneda (X : C) : PreservesLimit F (eCoyoneda V X) := by infer_instance

attribute [instance] HasConicalLimit.preservesLimit_eCoyoneda

variable (J) in
/--
Definition of `HasConicalLimitsOfShape` / `HasConicalLimitsOfShape` 的定义

English:
class HasConicalLimitsOfShape
  parameters: : Prop where
  axioms and operations (1):
    - hasConicalLimit : forall F : J ⥤ C, HasConicalLimit V F  [default: by infer_instance]

中文:
类 有余nicalLimitsOfShape
  参数: : 命题 where
  公理与运算 (1 个):
    - hasConicalLimit : 对任意 F : J ⥤ C, 有余nicalLimit V F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class HasConicalLimitsOfShape : Prop where
  /-- All functors `F : J ⥤ C` from `J` have limits. -/
  hasConicalLimit : forall F : J ⥤ C, HasConicalLimit V F := by infer_instance

attribute [instance] HasConicalLimitsOfShape.hasConicalLimit

/--
`C` has all conical limits of size `v₁ u₁` (`HasLimitsOfSize.{v₁ u₁} C`)
if it has conical limits of every shape `J : Type u₁` with `[Category.{v₁} J]`.
-/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the shape universes `v₁, u₁` would default
-- to universe output parameters. See Note [universe output parameters and typeclass caching].
@[univ_out_params, pp_with_univ]
/--
Definition of `HasConicalLimitsOfSize` / `HasConicalLimitsOfSize` 的定义

English:
class HasConicalLimitsOfSize
  parameters: : Prop where
  axioms and operations (1):
    - hasConicalLimitsOfShape : forall (J : Type u₁) [Category.{v₁} J], HasConicalLimitsOfShape J V C  [default: by infer_instance]

中文:
类 有余nicalLimitsOfSize
  参数: : 命题 where
  公理与运算 (1 个):
    - hasConicalLimitsOfShape : 对任意 (J : 类型u₁) [范畴.{v₁} J], 有余nicalLimitsOfShape J V C  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class HasConicalLimitsOfSize : Prop where
  /-- All functors `F : J ⥤ C` from all small `J` have conical limits -/
  hasConicalLimitsOfShape : forall (J : Type u₁) [Category.{v₁} J], HasConicalLimitsOfShape J V C := by
    infer_instance

attribute [instance] HasConicalLimitsOfSize.hasConicalLimitsOfShape

/--
Definition of `HasConicalLimits` / `HasConicalLimits` 的定义

English:
abbreviation HasConicalLimits
  signature: : Prop
  body: HasConicalLimitsOfSize.{v, v} V C

中文:
缩写 HasConicalLimits
  签名: : 命题
  定义体: HasConicalLimitsOfSize.{v, v} V C

Depends on / 依赖: HasConicalLimitsOfSize
-/
abbrev HasConicalLimits : Prop := HasConicalLimitsOfSize.{v, v} V C

end Definitions

section Results

variable {J : Type u₁} [Category.{v₁} J] {J' : Type u₂} [Category.{v₂} J']
variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- ensure existence of a conical limit implies existence of a limit -/
example (F : J ⥤ C) [HasConicalLimit V F] : HasLimit F := inferInstance

/--
lemma `HasConicalLimit.of_iso` / 引理 `HasConicalLimit.of_iso`

English:
lemma HasConicalLimit.of_iso
  given: {F G : J ⥤ C} [HasConicalLimit V F] (e : F ≅ G)
  proof: hasLimit_of_iso e
  preservesLimit_eCoyoneda X := preservesLimit_of_iso_diagram (eCoyoneda V X) e

中文:
引理 有余nicalLimit.of_iso
  条件: {F G : J ⥤ C} [有余nicalLimit V F] (e : F ≅ G)
  证明: hasLimit_of_iso e
  preservesLimit_eCoyoneda X := preservesLimit_of_iso_diagram (eCoyoneda V X) e

Depends on / 依赖: hasLimit_of_iso
-/
lemma HasConicalLimit.of_iso {F G : J ⥤ C} [HasConicalLimit V F] (e : F ≅ G) :
    HasConicalLimit V G where
  toHasLimit := hasLimit_of_iso e
  preservesLimit_eCoyoneda X := preservesLimit_of_iso_diagram (eCoyoneda V X) e

/--
Instance `HasConicalLimit.of_equiv` / 实例 `HasConicalLimit.of_equiv`

English:
instance HasConicalLimit.of_equiv
  signature: (F : J ⥤ C) [HasConicalLimit V F]

中文:
实例 有余nicalLimit.of_equiv
  签名: (F : J ⥤ C) [有余nicalLimit V F]

Depends on / 依赖: Discrete, Discrete.opposite, opposite, preservesColimitsOfShape_of_equiv
-/
instance HasConicalLimit.of_equiv (F : J ⥤ C) [HasConicalLimit V F]
    (G : J' ⥤ J) [G.IsEquivalence] : HasConicalLimit V (G ⋙ F) where

/--
lemma `HasConicalLimit.of_equiv_comp` / 引理 `HasConicalLimit.of_equiv_comp`

English:
lemma HasConicalLimit.of_equiv_comp
  statement: (F : J ⥤ C) (G : J' ⥤ J) [G.IsEquivalence]
  proof: have e : G.inv ⋙ G ⋙ F ≅ F := G.asEquivalence.invFunIdAssoc F
  HasConicalLimit.of_iso V e

中文:
引理 有余nicalLimit.of_equiv_comp
  结论: (F : J ⥤ C) (G : J' ⥤ J) [G.是等价]
  证明: have e : G.inv ⋙ G ⋙ F ≅ F := G.asEquivalence.invFunIdAssoc F
  HasConicalLimit.of_iso V e

Depends on / 依赖: G.asEquivalence.invFunIdAssoc, G.inv, HasConicalLimit, HasConicalLimit.of_iso, asEquivalence, invFunIdAssoc, of_iso
-/
lemma HasConicalLimit.of_equiv_comp (F : J ⥤ C) (G : J' ⥤ J) [G.IsEquivalence]
    [HasConicalLimit V (G ⋙ F)] : HasConicalLimit V F :=
  have e : G.inv ⋙ G ⋙ F ≅ F := G.asEquivalence.invFunIdAssoc F
  HasConicalLimit.of_iso V e

variable (C)

variable (J) in
/--
Instance `HasConicalLimitsOfShape.hasLimitsOfShape` / 实例 `HasConicalLimitsOfShape.hasLimitsOfShape`

English:
instance HasConicalLimitsOfShape.hasLimitsOfShape
  signature: [HasConicalLimitsOfShape J V C]

中文:
实例 有余nicalLimitsOfShape.hasLimitsOfShape
  签名: [有余nicalLimitsOfShape J V C]
-/
instance HasConicalLimitsOfShape.hasLimitsOfShape [HasConicalLimitsOfShape J V C] :
    HasLimitsOfShape J C where

/--
lemma `HasConicalLimitsOfShape.of_equiv` / 引理 `HasConicalLimitsOfShape.of_equiv`

English:
lemma HasConicalLimitsOfShape.of_equiv
  statement: [HasConicalLimitsOfShape J' V C]
  proof: HasConicalLimit.of_equiv_comp V F G

中文:
引理 有余nicalLimitsOfShape.of_equiv
  结论: [有余nicalLimitsOfShape J' V C]
  证明: HasConicalLimit.of_equiv_comp V F G

Depends on / 依赖: HasConicalLimit, HasConicalLimit.of_equiv_comp, of_equiv_comp
-/
lemma HasConicalLimitsOfShape.of_equiv [HasConicalLimitsOfShape J' V C]
    (G : J' ⥤ J) [G.IsEquivalence] : HasConicalLimitsOfShape J V C where
  hasConicalLimit F := HasConicalLimit.of_equiv_comp V F G

/--
Instance `HasConicalLimitsOfSize.hasLimitsOfSize` / 实例 `HasConicalLimitsOfSize.hasLimitsOfSize`

English:
instance HasConicalLimitsOfSize.hasLimitsOfSize
  signature: [HasConicalLimitsOfSize.{v₁, u₁} V C]

中文:
实例 有余nicalLimitsOfSize.hasLimitsOfSize
  签名: [有余nicalLimitsOfSize.{v₁, u₁} V C]
-/
instance HasConicalLimitsOfSize.hasLimitsOfSize [HasConicalLimitsOfSize.{v₁, u₁} V C] :
    HasLimitsOfSize.{v₁, u₁} C where

/-- ensure existence of (small) conical limits implies existence of (small) limits -/
example [HasConicalLimits V C] : HasLimits C := inferInstance

end Results

end CategoryTheory.Enriched
