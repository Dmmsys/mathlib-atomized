/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Idempotents.FunctorCategories

/-!

# Idempotent completeness of categories of simplicial objects

In this file, we provide an instance expressing that `SimplicialObject C`
and `CosimplicialObject C` are idempotent complete categories when the
category `C` is.

-/

public section


namespace CategoryTheory

namespace Idempotents

variable {C : Type*} [Category* C] [IsIdempotentComplete C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIdempotentComplete (SimplicialObject C)
  body: Idempotents.functor_category_isIdempotentComplete _ _

中文:
实例 :
  签名: IsIdempotentComplete (SimplicialObject C)
  定义体: Idempotents.functor_category_isIdempotentComplete _ _

Depends on / 依赖: Idempotents, Idempotents.functor_category_isIdempotentComplete, functor_category_isIdempotentComplete
-/
instance : IsIdempotentComplete (SimplicialObject C) :=
  Idempotents.functor_category_isIdempotentComplete _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIdempotentComplete (CosimplicialObject C)
  body: Idempotents.functor_category_isIdempotentComplete _ _

中文:
实例 :
  签名: IsIdempotentComplete (CosimplicialObject C)
  定义体: Idempotents.functor_category_isIdempotentComplete _ _

Depends on / 依赖: Idempotents, Idempotents.functor_category_isIdempotentComplete, functor_category_isIdempotentComplete
-/
instance : IsIdempotentComplete (CosimplicialObject C) :=
  Idempotents.functor_category_isIdempotentComplete _ _

end Idempotents

end CategoryTheory
