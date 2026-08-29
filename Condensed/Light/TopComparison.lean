/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Condensed.Light.Basic
public import Mathlib.Condensed.TopComparison

/-!

# The functor from topological spaces to light condensed sets

We define the functor `topCatToLightCondSet : TopCat.{u} ⥤ LightCondSet.{u}`.

-/

public section

universe u

open CategoryTheory

/--
Definition of `TopCat.toLightCondSet` / `TopCat.toLightCondSet` 的定义

English:
abbreviation TopCat.toLightCondSet
  signature: (X : TopCat.{u})
  body: toSheafCompHausLike.{u} _ X (fun _ _ _ => (LightProfinite.effectiveEpi_iff_surjective _).mp)

中文:
缩写 顶元素范畴.toLightCondSet
  签名: (X : 顶元素范畴.{u})
  定义体: toSheafCompHausLike.{u} _ X (fun _ _ _ => (LightProfinite.effectiveEpi_iff_surjective _).mp)

Depends on / 依赖: LightProfinite, LightProfinite.effectiveEpi_iff_surjective, effectiveEpi_iff_surjective, toSheafCompHausLike
-/
noncomputable abbrev TopCat.toLightCondSet (X : TopCat.{u}) : LightCondSet.{u} :=
  toSheafCompHausLike.{u} _ X (fun _ _ _ => (LightProfinite.effectiveEpi_iff_surjective _).mp)

/--
Definition of `topCatToLightCondSet` / `topCatToLightCondSet` 的定义

English:
abbreviation topCatToLightCondSet
  signature: : TopCat.{u} ⥤ LightCondSet.{u}
  body: topCatToSheafCompHausLike.{u} _ (fun _ _ _ => (LightProfinite.effectiveEpi_iff_surjective _).mp)

中文:
缩写 topCatToLightCondSet
  签名: : 顶元素范畴.{u} ⥤ LightCondSet.{u}
  定义体: topCatToSheafCompHausLike.{u} _ (fun _ _ _ => (LightProfinite.effectiveEpi_iff_surjective _).mp)

Depends on / 依赖: LightProfinite, LightProfinite.effectiveEpi_iff_surjective, effectiveEpi_iff_surjective, topCatToSheafCompHausLike
-/
noncomputable abbrev topCatToLightCondSet : TopCat.{u} ⥤ LightCondSet.{u} :=
  topCatToSheafCompHausLike.{u} _ (fun _ _ _ => (LightProfinite.effectiveEpi_iff_surjective _).mp)
