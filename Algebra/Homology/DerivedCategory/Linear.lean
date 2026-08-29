/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.CategoryTheory.Localization.Linear
public import Mathlib.CategoryTheory.Shift.Linear

/-!
# The derived category of a linear abelian category is linear

-/

public section

open CategoryTheory Category Limits Pretriangulated ZeroObject Preadditive

universe t w v u

variable (R : Type t) [Ring R] (C : Type u) [Category.{v} C] [Abelian C] [Linear R C]
  [HasDerivedCategory.{w} C]

namespace DerivedCategory

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Linear R (DerivedCategory C)
  body: Localization.linear R (DerivedCategory.Qh : _ ⥤ DerivedCategory C)
    (HomotopyCategory.quasiIso C _)

中文:
实例 :
  签名: Linear R (DerivedCategory C)
  定义体: Localization.linear R (DerivedCategory.Qh : _ ⥤ DerivedCategory C)
    (HomotopyCategory.quasiIso C _)

Depends on / 依赖: DerivedCategory, DerivedCategory.Qh, HomotopyCategory, HomotopyCategory.quasiIso, Localization, Localization.linear, linear, quasiIso
-/
noncomputable instance : Linear R (DerivedCategory C) :=
  Localization.linear R (DerivedCategory.Qh : _ ⥤ DerivedCategory C)
    (HomotopyCategory.quasiIso C _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor.Linear R (DerivedCategory.Qh : _ ⥤ DerivedCategory C)
  body: Localization.functor_linear _ _ _

中文:
实例 :
  签名: Functor.Linear R (DerivedCategory.Qh : _ ⥤ DerivedCategory C)
  定义体: Localization.functor_linear _ _ _

Depends on / 依赖: Localization, Localization.functor_linear, functor_linear
-/
instance : Functor.Linear R (DerivedCategory.Qh : _ ⥤ DerivedCategory C) :=
  Localization.functor_linear _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor.Linear R (DerivedCategory.Q : _ ⥤ DerivedCategory C)
  body: Functor.linear_of_iso _ (quotientCompQhIso C)

中文:
实例 :
  签名: Functor.Linear R (DerivedCategory.Q : _ ⥤ DerivedCategory C)
  定义体: Functor.linear_of_iso _ (quotientCompQhIso C)

Depends on / 依赖: Functor, Functor.linear_of_iso, linear_of_iso, quotientCompQhIso
-/
instance : Functor.Linear R (DerivedCategory.Q : _ ⥤ DerivedCategory C) :=
  Functor.linear_of_iso _ (quotientCompQhIso C)

instance (n : Int) : (shiftFunctor (DerivedCategory C) n).Linear R :=
  Shift.linear_of_localization R Qh (HomotopyCategory.subcategoryAcyclic C).trW _

instance (n : Int) : Functor.Linear R (DerivedCategory.singleFunctor C n) :=
  inferInstanceAs (Functor.Linear R (HomotopyCategory.singleFunctor C n ⋙ Qh))

end DerivedCategory
