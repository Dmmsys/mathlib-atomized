/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!

# HasExt instance for Module Category

If we assume `Small.{v} R`, the category `ModuleCat.{v} R` has enough projectives, which allows to
introduce the instance `HasExt.{v} (ModuleCat.{v} R)`. As a result, `Ext`-groups in this category
of modules are defined and belong to `Type v`.

-/

public section

universe v u

variable (R : Type u) [Ring R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{v}
  signature: R] : CategoryTheory.HasExt.{v} (ModuleCat.{v} R)
  body: CategoryTheory.hasExt_of_enoughProjectives.{v} (ModuleCat.{v} R)

中文:
实例 [Small.{v}
  签名: R] : CategoryTheory.HasExt.{v} (ModuleCat.{v} R)
  定义体: CategoryTheory.hasExt_of_enoughProjectives.{v} (ModuleCat.{v} R)

Depends on / 依赖: CategoryTheory, CategoryTheory.hasExt_of_enoughProjectives, ModuleCat, hasExt_of_enoughProjectives
-/
instance [Small.{v} R] : CategoryTheory.HasExt.{v} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{v} (ModuleCat.{v} R)
