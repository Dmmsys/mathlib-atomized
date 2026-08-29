/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Types.Basic

/-!
The hom functor, sending `(X, Y)` to the type `X ⟶ Y`.
-/

@[expose] public section


universe v u

open Opposite

open CategoryTheory

namespace CategoryTheory.Functor

variable (C : Type u) [Category.{v} C]

/-- `Functor.hom` is the hom-pairing, sending `(X, Y)` to `X ⟶ Y`, contravariant in `X` and
covariant in `Y`. -/
@[simps]
/--
Definition of `hom` / `hom` 的定义

English:
definition hom
  signature: : Cᵒᵖ × C ⥤ Type v where
  body: unop p.1 ⟶ p.2
  map f := ↾fun h => f.1.unop ≫ h ≫ f.2

中文:
定义 hom
  签名: : Cᵒᵖ × C ⥤ 类型v where
  定义体: unop p.1 ⟶ p.2
  map f := ↾fun h => f.1.unop ≫ h ≫ f.2

Depends on / 依赖: HasPullbacks, hasStrongEpiImages_of_hasPullbacks_of_hasEqualizers
-/
def hom : Cᵒᵖ × C ⥤ Type v where
  obj p := unop p.1 ⟶ p.2
  map f := ↾fun h => f.1.unop ≫ h ≫ f.2

end CategoryTheory.Functor
