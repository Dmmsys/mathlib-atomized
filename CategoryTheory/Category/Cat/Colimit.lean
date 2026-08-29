/-
Copyright (c) 2025 Mario Carneiro and Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
public import Mathlib.CategoryTheory.Monad.Limits


/-!
# The category of small categories has all small colimits.

In this file, the existence of colimits in `Cat` is deduced from the existence of colimits in the
category of simplicial sets. Indeed, `Cat` identifies to a reflective subcategory of the category
of simplicial sets (see `AlgebraicTopology.SimplicialSet.NerveAdjunction`), so that colimits in
`Cat` can be computed by passing to nerves, taking the colimit in `SSet` and finally applying the
homotopy category functor `SSet ⥤ Cat`.
-/

public section


noncomputable section

universe v

open CategoryTheory.Limits

namespace CategoryTheory

namespace Cat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasColimits Cat.{v, v}
  body: hasColimits_of_reflective nerveFunctor

中文:
实例 :
  签名: 有余极限 Cat.{v, v}
  定义体: hasColimits_of_reflective nerveFunctor

Depends on / 依赖: hasColimits_of_reflective, nerveFunctor
-/
instance : HasColimits Cat.{v, v} :=
  hasColimits_of_reflective nerveFunctor

end Cat

end CategoryTheory
