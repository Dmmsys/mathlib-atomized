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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EnrichedCategory SSet.{v} (SimplicialObject D)
  body: inferInstanceAs (EnrichedCategory (_ ⥤ Type v) (_ ⥤ D))

中文:
实例 :
  签名: EnrichedCategory SSet.{v} (SimplicialObject D)
  定义体: inferInstanceAs (EnrichedCategory (_ ⥤ Type v) (_ ⥤ D))

Depends on / 依赖: EnrichedCategory
-/
instance : EnrichedCategory SSet.{v} (SimplicialObject D) :=
  inferInstanceAs (EnrichedCategory (_ ⥤ Type v) (_ ⥤ D))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SimplicialCategory (SimplicialObject D)
  body: Functor.natTransEquiv.symm

中文:
实例 :
  签名: SimplicialCategory (SimplicialObject D)
  定义体: Functor.natTransEquiv.symm

Depends on / 依赖: Functor, Functor.natTransEquiv.symm, natTransEquiv
-/
instance : SimplicialCategory (SimplicialObject D) where
  homEquiv := Functor.natTransEquiv.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SimplicialCategory SSet.{v}
  body: inferInstanceAs (SimplicialCategory (SimplicialObject (Type v)))

中文:
实例 :
  签名: SimplicialCategory SSet.{v}
  定义体: inferInstanceAs (SimplicialCategory (SimplicialObject (Type v)))

Depends on / 依赖: SimplicialCategory, SimplicialObject
-/
instance : SimplicialCategory SSet.{v} :=
  inferInstanceAs (SimplicialCategory (SimplicialObject (Type v)))

end SimplicialObject

end CategoryTheory
