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

/-- Dinatural transformations between two difunctors. -/
/-
**CategoryTheory.DinatTrans** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：DinatTrans (F G : Cᵒᵖ ⥤ C ⥤ D) : Type max u₁ v₂ where /-- The component of
 a natural transformation. -/ app (X : C) : (F.obj (op X)).obj X ⟶ (G.obj (op X)
).obj X /-- The commutativity square for a given morphism. -/ dinaturality {X Y 
: C} (f : X ⟶ Y) : (F.map f.op).app X ≫ app X ≫ (G.obj (op X)).map f = (F.obj (o
p Y)).map f ≫ app Y ≫ (G.map f.op).app Y
参数：F G : Cᵒᵖ ⥤ C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dinatural transformations between two difunctors.
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
/-
**CategoryTheory.DinatTrans.compNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.DinatTrans`。
形式化陈述：compNatTrans (δ : F ⤞ G) (α : G ⟶ H) : F ⤞ H where app X
参数：δ : F ⤞ G；α : G ⟶ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Post-composition with a natural transformation.
-/
def compNatTrans (δ : F ⤞ G) (α : G ⟶ H) : F ⤞ H where
  app X := δ.app X ≫ (α.app (op X)).app X
  dinaturality f := by
    rw [Category.assoc, Category.assoc, ← NatTrans.naturality_app,
      ← δ.dinaturality_assoc f, NatTrans.naturality]

/-- Pre-composition with a natural transformation. -/
@[simps]
/-
**CategoryTheory.DinatTrans.precompNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.DinatTrans`。
形式化陈述：precompNatTrans (δ : G ⤞ H) (α : F ⟶ G) : F ⤞ H where app X
参数：δ : G ⤞ H；α : F ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pre-composition with a natural transformation.
-/
def precompNatTrans (δ : G ⤞ H) (α : F ⟶ G) : F ⤞ H where
  app X := (α.app (op X)).app X ≫ δ.app X

end DinatTrans
end CategoryTheory

