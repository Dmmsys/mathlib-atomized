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
/-
**CategoryTheory.Functor.hom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：hom : Cᵒᵖ × C ⥤ Type v where obj p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Functor.hom` is the hom-pairing, sending `(X, Y)` to `X ⟶ Y`, contravariant in 
`X` and
covariant in `Y`.
-/
def hom : Cᵒᵖ × C ⥤ Type v where
  obj p := unop p.1 ⟶ p.2
  map f := ↾fun h => f.1.unop ≫ h ≫ f.2

end CategoryTheory.Functor

