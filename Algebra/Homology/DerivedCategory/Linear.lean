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

/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Linear R (DerivedCategory C) :=
  Localization.linear R (DerivedCategory.Qh : _ ⥤ DerivedCategory C)
    (HomotopyCategory.quasiIso C _)
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Functor.Linear R (DerivedCategory.Qh : _ ⥤ DerivedCategory C) :=
  Localization.functor_linear _ _ _
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Functor.Linear R (DerivedCategory.Q : _ ⥤ DerivedCategory C) :=
  Functor.linear_of_iso _ (quotientCompQhIso C)
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : (shiftFunctor (DerivedCategory C) n).Linear R :=
  Shift.linear_of_localization R Qh (HomotopyCategory.subcategoryAcyclic C).trW _
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : Functor.Linear R (DerivedCategory.singleFunctor C n) :=
  inferInstanceAs (Functor.Linear R (HomotopyCategory.singleFunctor C n ⋙ Qh))

end DerivedCategory

