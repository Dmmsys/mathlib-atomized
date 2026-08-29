/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.Condensed.Functors
public import Mathlib.Condensed.Limits

/-!

# Solid modules

This file contains the definition of a solid `R`-module: `CondensedMod.isSolid R`. Solid modules
groups were introduced in [scholze2019condensed], Definition 5.1.

## Main definition

* `CondensedMod.IsSolid R`: the predicate on condensed `R`-modules describing the property of
  being solid.

TODO (hard): prove that `((profiniteSolid ℤ).obj S).IsSolid` for `S : Profinite`.
TODO (slightly easier): prove that `((profiniteSolid 𝔽ₚ).obj S).IsSolid` for `S : Profinite`.
-/

@[expose] public section

universe u

variable (R : Type (u + 1)) [Ring R]

open CategoryTheory Limits Profinite Condensed

noncomputable section

namespace Condensed

/--
Definition of `finFree` / `finFree` 的定义

English:
abbreviation finFree
  signature: : FintypeCat.{u} ⥤ CondensedMod.{u} R
  body: FintypeCat.toProfinite ⋙ profiniteToCondensed ⋙ free R

中文:
缩写 finFree
  签名: : FintypeCat.{u} ⥤ CondensedMod.{u} R
  定义体: FintypeCat.toProfinite ⋙ profiniteToCondensed ⋙ free R

Depends on / 依赖: FintypeCat, FintypeCat.toProfinite, profiniteToCondensed, toProfinite
-/
abbrev finFree : FintypeCat.{u} ⥤ CondensedMod.{u} R :=
  FintypeCat.toProfinite ⋙ profiniteToCondensed ⋙ free R

/--
Definition of `profiniteFree` / `profiniteFree` 的定义

English:
abbreviation profiniteFree
  signature: : Profinite.{u} ⥤ CondensedMod.{u} R
  body: profiniteToCondensed ⋙ free R

中文:
缩写 profiniteFree
  签名: : Profinite.{u} ⥤ CondensedMod.{u} R
  定义体: profiniteToCondensed ⋙ free R

Depends on / 依赖: profiniteToCondensed
-/
abbrev profiniteFree : Profinite.{u} ⥤ CondensedMod.{u} R :=
  profiniteToCondensed ⋙ free R

/--
Definition of `profiniteSolid` / `profiniteSolid` 的定义

English:
definition profiniteSolid
  signature: : Profinite.{u} ⥤ CondensedMod.{u} R
  body: Functor.rightKanExtension FintypeCat.toProfinite (finFree R)

中文:
定义 profiniteSolid
  签名: : Profinite.{u} ⥤ CondensedMod.{u} R
  定义体: Functor.rightKanExtension FintypeCat.toProfinite (finFree R)

Depends on / 依赖: FintypeCat, FintypeCat.toProfinite, Functor, Functor.rightKanExtension, finFree, rightKanExtension, toProfinite
-/
def profiniteSolid : Profinite.{u} ⥤ CondensedMod.{u} R :=
  Functor.rightKanExtension FintypeCat.toProfinite (finFree R)

/--
Definition of `profiniteSolidCounit` / `profiniteSolidCounit` 的定义

English:
definition profiniteSolidCounit
  signature: : FintypeCat.toProfinite ⋙ profiniteSolid R ⟶ finFree R
  body: Functor.rightKanExtensionCounit FintypeCat.toProfinite (finFree R)

中文:
定义 profiniteSolidCounit
  签名: : FintypeCat.toProfinite ⋙ profiniteSolid R ⟶ finFree R
  定义体: Functor.rightKanExtensionCounit FintypeCat.toProfinite (finFree R)

Depends on / 依赖: FintypeCat, FintypeCat.toProfinite, Functor, Functor.rightKanExtensionCounit, finFree, rightKanExtensionCounit, toProfinite
-/
def profiniteSolidCounit : FintypeCat.toProfinite ⋙ profiniteSolid R ⟶ finFree R :=
  Functor.rightKanExtensionCounit FintypeCat.toProfinite (finFree R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (profiniteSolid R).IsRightKanExtension (profiniteSolidCounit R)
  body: by
  dsimp only [profiniteSolidCounit, profiniteSolid]
  infer_instance

中文:
实例 :
  签名: (profiniteSolid R).IsRightKanExtension (profiniteSolidCounit R)
  定义体: by
  dsimp only [profiniteSolidCounit, profiniteSolid]
  infer_instance

Depends on / 依赖: infer_instance, profiniteSolid, profiniteSolidCounit
-/
instance : (profiniteSolid R).IsRightKanExtension (profiniteSolidCounit R) := by
  dsimp only [profiniteSolidCounit, profiniteSolid]
  infer_instance

/--
Definition of `profiniteSolidIsPointwiseRightKanExtension` / `profiniteSolidIsPointwiseRightKanExtension` 的定义

English:
definition profiniteSolidIsPointwiseRightKanExtension
  signature: :
  body: Functor.isPointwiseRightKanExtensionOfIsRightKanExtension _ _

中文:
定义 profiniteSolidIsPointwiseRightKanExtension
  签名: :
  定义体: Functor.isPointwiseRightKanExtensionOfIsRightKanExtension _ _

Depends on / 依赖: Functor, Functor.isPointwiseRightKanExtensionOfIsRightKanExtension, isPointwiseRightKanExtensionOfIsRightKanExtension
-/
def profiniteSolidIsPointwiseRightKanExtension :
    (Functor.RightExtension.mk _ (profiniteSolidCounit R)).IsPointwiseRightKanExtension :=
  Functor.isPointwiseRightKanExtensionOfIsRightKanExtension _ _

/--
Definition of `profiniteSolidification` / `profiniteSolidification` 的定义

English:
definition profiniteSolidification
  signature: : profiniteFree R ⟶ profiniteSolid.{u} R
  body: (profiniteSolid R).liftOfIsRightKanExtension (profiniteSolidCounit R) _ (𝟙 _)

中文:
定义 profiniteSolidification
  签名: : profiniteFree R ⟶ profiniteSolid.{u} R
  定义体: (profiniteSolid R).liftOfIsRightKanExtension (profiniteSolidCounit R) _ (𝟙 _)

Depends on / 依赖: liftOfIsRightKanExtension, profiniteSolid, profiniteSolidCounit
-/
def profiniteSolidification : profiniteFree R ⟶ profiniteSolid.{u} R :=
  (profiniteSolid R).liftOfIsRightKanExtension (profiniteSolidCounit R) _ (𝟙 _)

end Condensed

/--
Definition of `CondensedMod.IsSolid` / `CondensedMod.IsSolid` 的定义

English:
class CondensedMod.IsSolid
  parameters: (A : CondensedMod.{u} R)
  axioms and operations (1):
    - isIso_solidification_map : forall X : Profinite.{u}, IsIso ((yoneda.obj A).map ((profiniteSolidification R).app X).op)

中文:
类 CondensedMod.IsSolid
  参数: (A : CondensedMod.{u} R)
  公理与运算 (1 个):
    - isIso_solidification_map : 对任意 X : Profinite.{u}, IsIso ((yoneda.obj A).map ((profiniteSolidification R).app X).op)
-/
class CondensedMod.IsSolid (A : CondensedMod.{u} R) : Prop where
  isIso_solidification_map : forall X : Profinite.{u}, IsIso ((yoneda.obj A).map
    ((profiniteSolidification R).app X).op)
