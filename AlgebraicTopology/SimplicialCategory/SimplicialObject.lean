/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
public import Mathlib.CategoryTheory.Functor.FunctorHom

/-!
# The category of simplicial objects is simplicial

In `CategoryTheory.Functor.FunctorHom`, it was shown that a category of functors
`C ⥤ D` is enriched over a suitable category `C ⥤ Type _` of functors to types.

In this file, we deduce that `SimplicialObject D` is enriched over `SSet.{v} D`
(when `D : Type u` and `[Category.{v} D]`) and that `SimplicialObject D`
is actually a simplicial category. In particular, the category of simplicial
sets is a simplicial category.

-/

public section

universe v u

namespace CategoryTheory

variable {D : Type u} [Category.{v} D]

namespace SimplicialObject

/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EnrichedCategory SSet.{v} (SimplicialObject D) :=
  inferInstanceAs (EnrichedCategory (_ ⥤ Type v) (_ ⥤ D))
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SimplicialCategory (SimplicialObject D) where
  homEquiv := Functor.natTransEquiv.symm
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SimplicialCategory SSet.{v} :=
  inferInstanceAs (SimplicialCategory (SimplicialObject (Type v)))

end SimplicialObject

end CategoryTheory

