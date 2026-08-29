/-
Copyright (c) 2019 Kim Morrison, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Functor.Category

/-!
# Thin categories

A thin category (also known as a sparse category) is a category with at most one morphism between
each pair of objects.
Examples include posets, but also some indexing categories (diagrams) for special shapes of
(co)limits.
To construct a category instance one only needs to specify the `CategoryStruct` part,
as the axioms hold for free.
If `C` is thin, then the category of functors to `C` is also thin.
Further, to show two objects are isomorphic in a thin category, it suffices only to give a morphism
in each direction.
-/

@[expose] public section


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁}

section

variable [CategoryStruct.{v₁} C] [Quiver.IsThin C]

/-- Construct a category instance from a `CategoryStruct`, using the fact that
    hom spaces are subsingletons to prove the axioms. -/
@[instance_reducible]
/--
Definition of `thin_category` / `thin_category` 的定义

English:
definition thin_category
  signature: : Category C where

中文:
定义 thin_category
  签名: : 范畴 C where
-/
def thin_category : Category C where

end

-- We don't assume anything about where the category instance on `C` came from.
-- In particular this allows `C` to be a preorder, with the category instance inherited from the
-- preorder structure.
variable [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable [Quiver.IsThin C]

/--
Instance `functor_thin` / 实例 `functor_thin`

English:
instance functor_thin
  signature: : Quiver.IsThin (D ⥤ C)
  body: fun _ _ =>
  ⟨fun α β => NatTrans.ext (by subsingleton)⟩

中文:
实例 functor_thin
  签名: : 箭图.IsThin (D ⥤ C)
  定义体: fun _ _ =>
  ⟨fun α β => NatTrans.ext (by subsingleton)⟩
-/
instance functor_thin : Quiver.IsThin (D ⥤ C) := fun _ _ =>
  ⟨fun α β => NatTrans.ext (by subsingleton)⟩

/--
Definition of `iso_of_both_ways` / `iso_of_both_ways` 的定义

English:
definition iso_of_both_ways
  signature: {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X)
  body: f
  inv := g

中文:
定义 iso_of_both_ways
  签名: {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X)
  定义体: f
  inv := g
-/
def iso_of_both_ways {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) :
    X ≅ Y where
  hom := f
  inv := g

/--
Instance `subsingleton_iso` / 实例 `subsingleton_iso`

English:
instance subsingleton_iso
  signature: {X Y : C}
  body: ⟨by
    intro i₁ i₂
    ext1
    subsingleton⟩

中文:
实例 subsingleton_iso
  签名: {X Y : C}
  定义体: ⟨by
    intro i₁ i₂
    ext1
    subsingleton⟩

Depends on / 依赖: subsingleton
-/
instance subsingleton_iso {X Y : C} : Subsingleton (X ≅ Y) :=
  ⟨by
    intro i₁ i₂
    ext1
    subsingleton⟩

end CategoryTheory
