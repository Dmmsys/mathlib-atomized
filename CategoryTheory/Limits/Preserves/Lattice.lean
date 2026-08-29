/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Hom.CompleteLattice

/-!
# Lattice Homs that Preserve Limits and Colimits

This file provides instances for when OrderHom.toFunctor preserves limits/colimits.
In particular, if `f` preserves finite infs/sups (i.e. is from a InfTopHomClass/SupBotHomClass)
then `(toOrderHom f).toFunctor` preserves finite limits/colimits. If `f` preserves
arbitrary infs/sups (i.e. is from a sInfHomClass/sSupHomClass) then `(toOrderHom f).toFunctor`
preserves all limits/colimits.

-/

public section

open OrderHomClass

namespace CategoryTheory.Limits.CompleteLattice

universe w w' u v

variable {α : Type u} {β : Type v} {F : Type*} [FunLike F α β] (f : F)

section

variable [SemilatticeInf α] [OrderTop α] [SemilatticeInf β] [OrderTop β] [InfTopHomClass F α β]

/--
Instance `preservesLimit_finite_toFunctor` / 实例 `preservesLimit_finite_toFunctor`

English:
instance preservesLimit_finite_toFunctor
  signature: {J : Type w} [SmallCategory J]
  body: preservesLimit_of_preserves_limit_cone (finiteLimitCone K).isLimit
    (finiteLimitCone _).isLimit.ofIsoLimit
      (Cone.ext (eqToIso (show Finset.univ.inf _ = f _ by aesop)) (by subsingleton))

中文:
实例 preservesLimit_finite_toFunctor
  签名: {J : 类型 w} [小范畴 J]
  定义体: preservesLimit_of_preserves_limit_cone (finiteLimitCone K).isLimit
    (finiteLimitCone _).isLimit.ofIsoLimit
      (Cone.ext (eqToIso (show Finset.univ.inf _ = f _ by aesop)) (by subsingleton))

Depends on / 依赖: Cone.ext, Finset, Finset.univ.inf, eqToIso, finiteLimitCone, isLimit, isLimit.ofIsoLimit, ofIsoLimit, preservesLimit_of_preserves_limit_cone, subsingleton
-/
instance preservesLimit_finite_toFunctor {J : Type w} [SmallCategory J]
    [FinCategory J] (K : J ⥤ α) : PreservesLimit K (toOrderHom f).toFunctor :=
preservesLimit_of_preserves_limit_cone (finiteLimitCone K).isLimit
    (finiteLimitCone _).isLimit.ofIsoLimit
      (Cone.ext (eqToIso (show Finset.univ.inf _ = f _ by aesop)) (by subsingleton))

/--
Instance `preservesLimitsOfShape_finite_toFunctor` / 实例 `preservesLimitsOfShape_finite_toFunctor`

English:
instance preservesLimitsOfShape_finite_toFunctor
  signature: {J : Type w} [SmallCategory J] [FinCategory J]

中文:
实例 preservesLimitsOfShape_finite_toFunctor
  签名: {J : 类型 w} [小范畴 J] [有限范畴 J]
-/
instance preservesLimitsOfShape_finite_toFunctor {J : Type w} [SmallCategory J] [FinCategory J] :
    PreservesLimitsOfShape J (toOrderHom f).toFunctor where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteLimits (toOrderHom f).toFunctor
  body: inferInstance

中文:
实例 :
  签名: 保持FiniteLimits (toOrderHom f).toFunctor
  定义体: inferInstance
-/
instance : PreservesFiniteLimits (toOrderHom f).toFunctor where
  preservesFiniteLimits _ _ _ := inferInstance

end

section

variable [SemilatticeSup α] [OrderBot α] [SemilatticeSup β] [OrderBot β] [SupBotHomClass F α β]

/--
Instance `preservesColimit_finite_toFunctor` / 实例 `preservesColimit_finite_toFunctor`

English:
instance preservesColimit_finite_toFunctor
  signature: {J : Type w} [SmallCategory J]
  body: preservesColimit_of_preserves_colimit_cocone (finiteColimitCocone K).isColimit
    (finiteColimitCocone _).isColimit.ofIsoColimit
      (Cocone.ext (eqToIso (show Finset.univ.sup _ = f _ by aesop)) (by subsingleton))

中文:
实例 preservesColimit_finite_toFunctor
  签名: {J : 类型 w} [小范畴 J]
  定义体: preservesColimit_of_preserves_colimit_cocone (finiteColimitCocone K).isColimit
    (finiteColimitCocone _).isColimit.ofIsoColimit
      (Cocone.ext (eqToIso (show Finset.univ.sup _ = f _ by aesop)) (by subsingleton))

Depends on / 依赖: Cocone, Cocone.ext, Finset, Finset.univ.sup, eqToIso, finiteColimitCocone, isColimit, isColimit.ofIsoColimit, ofIsoColimit, preservesColimit_of_preserves_colimit_cocone, subsingleton
-/
instance preservesColimit_finite_toFunctor {J : Type w} [SmallCategory J]
    [FinCategory J] (K : J ⥤ α) : PreservesColimit K (toOrderHom f).toFunctor :=
preservesColimit_of_preserves_colimit_cocone (finiteColimitCocone K).isColimit
    (finiteColimitCocone _).isColimit.ofIsoColimit
      (Cocone.ext (eqToIso (show Finset.univ.sup _ = f _ by aesop)) (by subsingleton))

/--
Instance `preservesColimitsOfShape_finite_toFunctor` / 实例 `preservesColimitsOfShape_finite_toFunctor`

English:
instance preservesColimitsOfShape_finite_toFunctor
  signature: {J : Type w} [SmallCategory J]

中文:
实例 preservesColimitsOfShape_finite_toFunctor
  签名: {J : 类型 w} [小范畴 J]
-/
instance preservesColimitsOfShape_finite_toFunctor {J : Type w} [SmallCategory J]
    [FinCategory J] : PreservesColimitsOfShape J (toOrderHom f).toFunctor where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteColimits (toOrderHom f).toFunctor
  body: inferInstance

中文:
实例 :
  签名: 保持FiniteColimits (toOrderHom f).toFunctor
  定义体: inferInstance
-/
instance : PreservesFiniteColimits (toOrderHom f).toFunctor where
  preservesFiniteColimits _ _ _ := inferInstance

end

section

variable [CompleteLattice α] [CompleteLattice β]

/--
Instance `preservesLimit_toFunctor` / 实例 `preservesLimit_toFunctor`

English:
instance preservesLimit_toFunctor
  signature: [sInfHomClass F α β] {J : Type w} [Category.{w'} J]
  body: preservesLimit_of_preserves_limit_cone (limitCone K).isLimit
    (limitCone _).isLimit.ofIsoLimit (Cone.ext (eqToIso (by aesop)) (by subsingleton))

中文:
实例 preservesLimit_toFunctor
  签名: [sInf态射类 F α β] {J : 类型 w} [范畴.{w'} J]
  定义体: preservesLimit_of_preserves_limit_cone (limitCone K).isLimit
    (limitCone _).isLimit.ofIsoLimit (Cone.ext (eqToIso (by aesop)) (by subsingleton))

Depends on / 依赖: Cone.ext, eqToIso, isLimit, isLimit.ofIsoLimit, limitCone, ofIsoLimit, preservesLimit_of_preserves_limit_cone, subsingleton
-/
instance preservesLimit_toFunctor [sInfHomClass F α β] {J : Type w} [Category.{w'} J]
    (K : J ⥤ α) : PreservesLimit K (toOrderHom f).toFunctor :=
preservesLimit_of_preserves_limit_cone (limitCone K).isLimit
    (limitCone _).isLimit.ofIsoLimit (Cone.ext (eqToIso (by aesop)) (by subsingleton))

/--
Instance `preservesLimitsOfShape_toFunctor` / 实例 `preservesLimitsOfShape_toFunctor`

English:
instance preservesLimitsOfShape_toFunctor
  signature: [sInfHomClass F α β] {J : Type w} [Category.{w'} J]

中文:
实例 preservesLimitsOfShape_toFunctor
  签名: [sInf态射类 F α β] {J : 类型 w} [范畴.{w'} J]
-/
instance preservesLimitsOfShape_toFunctor [sInfHomClass F α β] {J : Type w} [Category.{w'} J] :
    PreservesLimitsOfShape J (toOrderHom f).toFunctor where

/--
Instance `preservesLimitsOfSize_toFunctor` / 实例 `preservesLimitsOfSize_toFunctor`

English:
instance preservesLimitsOfSize_toFunctor
  signature: [sInfHomClass F α β]

中文:
实例 preservesLimitsOfSize_toFunctor
  签名: [sInf态射类 F α β]
-/
instance preservesLimitsOfSize_toFunctor [sInfHomClass F α β] :
    PreservesLimitsOfSize.{w', w} (toOrderHom f).toFunctor where

/--
Instance `preservesLimits_toFunctor` / 实例 `preservesLimits_toFunctor`

English:
instance preservesLimits_toFunctor
  signature: [sInfHomClass F α β]

中文:
实例 preservesLimits_toFunctor
  签名: [sInf态射类 F α β]
-/
instance preservesLimits_toFunctor [sInfHomClass F α β] :
    PreservesLimits (toOrderHom f).toFunctor where

/--
Instance `preservesColimit_toFunctor` / 实例 `preservesColimit_toFunctor`

English:
instance preservesColimit_toFunctor
  signature: [sSupHomClass F α β] {J : Type w} [Category.{w'} J]
  body: preservesColimit_of_preserves_colimit_cocone (colimitCocone K).isColimit
    (colimitCocone _).isColimit.ofIsoColimit (Cocone.ext (eqToIso (by aesop)) (by subsingleton))

中文:
实例 preservesColimit_toFunctor
  签名: [sSup态射类 F α β] {J : 类型 w} [范畴.{w'} J]
  定义体: preservesColimit_of_preserves_colimit_cocone (colimitCocone K).isColimit
    (colimitCocone _).isColimit.ofIsoColimit (Cocone.ext (eqToIso (by aesop)) (by subsingleton))

Depends on / 依赖: Cocone, Cocone.ext, colimitCocone, eqToIso, isColimit, isColimit.ofIsoColimit, ofIsoColimit, preservesColimit_of_preserves_colimit_cocone, subsingleton
-/
instance preservesColimit_toFunctor [sSupHomClass F α β] {J : Type w} [Category.{w'} J]
    (K : J ⥤ α) : PreservesColimit K (toOrderHom f).toFunctor :=
preservesColimit_of_preserves_colimit_cocone (colimitCocone K).isColimit
    (colimitCocone _).isColimit.ofIsoColimit (Cocone.ext (eqToIso (by aesop)) (by subsingleton))

/--
Instance `preservesColimitsOfShape_toFunctor` / 实例 `preservesColimitsOfShape_toFunctor`

English:
instance preservesColimitsOfShape_toFunctor
  signature: [sSupHomClass F α β] {J : Type w} [Category.{w'} J]

中文:
实例 preservesColimitsOfShape_toFunctor
  签名: [sSup态射类 F α β] {J : 类型 w} [范畴.{w'} J]
-/
instance preservesColimitsOfShape_toFunctor [sSupHomClass F α β] {J : Type w} [Category.{w'} J] :
    PreservesColimitsOfShape J (toOrderHom f).toFunctor where

/--
Instance `preservesColimitsOfSize_toFunctor` / 实例 `preservesColimitsOfSize_toFunctor`

English:
instance preservesColimitsOfSize_toFunctor
  signature: [sSupHomClass F α β]

中文:
实例 preservesColimitsOfSize_toFunctor
  签名: [sSup态射类 F α β]
-/
instance preservesColimitsOfSize_toFunctor [sSupHomClass F α β] :
    PreservesColimitsOfSize.{w', w} (toOrderHom f).toFunctor where

/--
Instance `preservesColimits_toFunctor` / 实例 `preservesColimits_toFunctor`

English:
instance preservesColimits_toFunctor
  signature: [sSupHomClass F α β]

中文:
实例 preservesColimits_toFunctor
  签名: [sSup态射类 F α β]
-/
instance preservesColimits_toFunctor [sSupHomClass F α β] :
    PreservesColimits (toOrderHom f).toFunctor where

end

end CategoryTheory.Limits.CompleteLattice
