/-
Copyright (c) 2025 Pablo Donato. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Donato
-/
module

public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Subobjects presheaf

Following Section I.3 of [Sheaves in Geometry and Logic][MM92], we define the subobjects presheaf
`Subobject.presheaf C` mapping any object `X` to its type of subobjects `Subobject X`.

## Main definitions

Let `C` refer to a category with pullbacks.

* `CategoryTheory.Subobject.presheaf C` is the presheaf that sends every object `X : C` to its type
  of subobjects `Subobject X`, and every morphism `f : X ⟶ Y` to the function `Subobject Y →
  Subobject X` that maps every subobject of `Y` to its pullback along `f`.

## References

* [S. MacLane and I. Moerdijk, *Sheaves in geometry and logic: A first introduction to topos
  theory*][MM92]

## Tags

subobject, representable functor, presheaf, topos theory
-/

@[expose] public section

open CategoryTheory Subobject

namespace Subobject

universe u v

variable (C : Type u) [Category.{v} C] [Limits.HasPullbacks C]

/-- This is the presheaf that sends every object `X : C` to its type of subobjects `Subobject X`,
and every morphism `f : X ⟶ Y` to the function `Subobject Y → Subobject X` that maps every
subobject of `Y` to its pullback along `f`. -/
@[simps]
/--
Definition of `presheaf` / `presheaf` 的定义

English:
definition presheaf
  signature: : Cᵒᵖ ⥤ Type max u v where
  body: Subobject X.unop
  map f := ↾(pullback f.unop).obj
  map_id _ := by ext : 3; simp [pullback_id]
  map_comp _ _ := by ext : 3; simp [pullback_comp]

中文:
定义 presheaf
  签名: : Cᵒᵖ ⥤ 类型 最大值 u v where
  定义体: Subobject X.unop
  map f := ↾(pullback f.unop).obj
  map_id _ := by ext : 3; simp [pullback_id]
  map_comp _ _ := by ext : 3; simp [pullback_comp]

Depends on / 依赖: Subobject, X.unop
-/
noncomputable def presheaf : Cᵒᵖ ⥤ Type max u v where
  obj X := Subobject X.unop
  map f := ↾(pullback f.unop).obj
  map_id _ := by ext : 3; simp [pullback_id]
  map_comp _ _ := by ext : 3; simp [pullback_comp]

end Subobject
