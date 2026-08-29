/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Functor.RegularEpi

/-!
# The category of simplicial sets is a regular epi category

-/

public section

universe u

open CategoryTheory

namespace SSet

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsRegularEpiCategory SSet.{u}
  body: inferInstanceAs (IsRegularEpiCategory (_ ⥤ _))

中文:
实例 :
  签名: IsRegularEpiCategory SSet.{u}
  定义体: inferInstanceAs (IsRegularEpiCategory (_ ⥤ _))

Depends on / 依赖: IsRegularEpiCategory
-/
instance : IsRegularEpiCategory SSet.{u} :=
  inferInstanceAs (IsRegularEpiCategory (_ ⥤ _))

end SSet
