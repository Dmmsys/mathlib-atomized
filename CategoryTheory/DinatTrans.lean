/-
Copyright (c) 2023 Andrea Laretto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Laretto, Fernando Chu
-/
module

public import Mathlib.CategoryTheory.Opposites

/-!
# Dinatural transformations

Dinatural transformations are special kinds of transformations between
functors `F G : Cᵒᵖ ⥤ C ⥤ D` which depend both covariantly and contravariantly
on the same category (also known as difunctors).

A dinatural transformation is a family of morphisms given only on *the diagonal* of the two
functors, and is such that a certain naturality hexagon commutes.
Note that dinatural transformations cannot be composed with each other (since the outer
hexagon does not commute in general), but can still be "pre/post-composed" with
ordinary natural transformations.

## References
* <https://ncatlab.org/nlab/show/dinatural+transformation>
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

open Opposite

/--
Definition of `DinatTrans` / `DinatTrans` 的定义

English:
structure DinatTrans
  parameters: (F G : Cᵒᵖ ⥤ C ⥤ D)
  axioms and operations (2):
    - app((X : C)) : (F.obj (op X)).obj X ⟶ (G.obj (op X)).obj X
    - dinaturality({X Y : C} (f : X ⟶ Y)) : (F.map f.op).app X ≫ app X ≫ (G.obj (op X)).map f = (F.obj (op Y)).map f ≫ app Y ≫ (G.map f.op).app Y  [default: by cat_disch]

中文:
结构 DinatTrans
  参数: (F G : Cᵒᵖ ⥤ C ⥤ D)
  公理与运算 (2 个):
    - app((X : C)) : (F.obj (op X)).obj X ⟶ (G.obj (op X)).obj X
    - dinaturality({X Y : C} (f : X ⟶ Y)) : (F.map f.op).app X ≫ app X ≫ (G.obj (op X)).map f = (F.obj (op Y)).map f ≫ app Y ≫ (G.map f.op).app Y  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure DinatTrans (F G : Cᵒᵖ ⥤ C ⥤ D) : Type max u₁ v₂ where
  /-- The component of a natural transformation. -/
  app (X : C) : (F.obj (op X)).obj X ⟶ (G.obj (op X)).obj X
  /-- The commutativity square for a given morphism. -/
  dinaturality {X Y : C} (f : X ⟶ Y) :
    (F.map f.op).app X ≫ app X ≫ (G.obj (op X)).map f =
    (F.obj (op Y)).map f ≫ app Y ≫ (G.map f.op).app Y := by cat_disch

attribute [reassoc (attr := simp)] DinatTrans.dinaturality

namespace DinatTrans

/-- Notation for dinatural transformations. -/
scoped infixr:50 " ⤞ " => DinatTrans

variable {F G H : Cᵒᵖ ⥤ C ⥤ D}

/-- Post-composition with a natural transformation. -/
@[simps]
/--
Definition of `compNatTrans` / `compNatTrans` 的定义

English:
definition compNatTrans
  signature: (δ : F ⤞ G) (α : G ⟶ H)
  body: δ.app X ≫ (α.app (op X)).app X
  dinaturality f := by
    rw [Category.assoc]; rw [Category.assoc]; rw [← NatTrans.naturality_app]; rw [← δ.dinaturality_assoc f]; rw [NatTrans.naturality]

中文:
定义 comp自然数Trans
  签名: (δ : F ⤞ G) (α : G ⟶ H)
  定义体: δ.app X ≫ (α.app (op X)).app X
  dinaturality f := by
    rw [Category.assoc]; rw [Category.assoc]; rw [← NatTrans.naturality_app]; rw [← δ.dinaturality_assoc f]; rw [NatTrans.naturality]
-/
def compNatTrans (δ : F ⤞ G) (α : G ⟶ H) : F ⤞ H where
  app X := δ.app X ≫ (α.app (op X)).app X
  dinaturality f := by
    rw [Category.assoc]; rw [Category.assoc]; rw [← NatTrans.naturality_app]; rw [← δ.dinaturality_assoc f]; rw [NatTrans.naturality]

/-- Pre-composition with a natural transformation. -/
@[simps]
/--
Definition of `precompNatTrans` / `precompNatTrans` 的定义

English:
definition precompNatTrans
  signature: (δ : G ⤞ H) (α : F ⟶ G)
  body: (α.app (op X)).app X ≫ δ.app X

中文:
定义 precomp自然数Trans
  签名: (δ : G ⤞ H) (α : F ⟶ G)
  定义体: (α.app (op X)).app X ≫ δ.app X
-/
def precompNatTrans (δ : G ⤞ H) (α : F ⟶ G) : F ⤞ H where
  app X := (α.app (op X)).app X ≫ δ.app X

end DinatTrans
end CategoryTheory
