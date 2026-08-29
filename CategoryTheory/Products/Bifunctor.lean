/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Products.Basic

/-!
# Lemmas about functors out of product categories.
-/

public section


open CategoryTheory

namespace CategoryTheory.Bifunctor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]

open scoped CategoryTheory.Prod

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (F : C × D ⥤ E) (X : C) (Y : D)
  proof: F.map_id (X, Y)

@[simp]

中文:
定理 map_id
  条件: (F : C × D ⥤ E) (X : C) (Y : D)
  证明: F.map_id (X, Y)

@[simp]

Depends on / 依赖: F.map_id, map_id
-/
theorem map_id (F : C × D ⥤ E) (X : C) (Y : D) :
    F.map ((𝟙 X) ×ₘ (𝟙 Y)) = 𝟙 (F.obj (X, Y)) :=
  F.map_id (X, Y)

@[simp]
/--
theorem `map_id_comp` / 定理 `map_id_comp`

English:
theorem map_id_comp
  given: (F : C × D ⥤ E) (W : C) {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: by
  rw [← Functor.map_comp]; rw [prod_comp]; rw [Category.comp_id]

@[simp]

中文:
定理 map_id_comp
  条件: (F : C × D ⥤ E) (W : C) {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: by
  rw [← Functor.map_comp]; rw [prod_comp]; rw [Category.comp_id]

@[simp]

Depends on / 依赖: Category, Category.comp_id, Functor, Functor.map_comp, comp_id, map_comp, prod_comp
-/
theorem map_id_comp (F : C × D ⥤ E) (W : C) {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (𝟙 W ×ₘ (f ≫ g)) = F.map (𝟙 W ×ₘ f) ≫ F.map (𝟙 W ×ₘ g) := by
  rw [← Functor.map_comp]; rw [prod_comp]; rw [Category.comp_id]

@[simp]
/--
theorem `map_comp_id` / 定理 `map_comp_id`

English:
theorem map_comp_id
  given: (F : C × D ⥤ E) (X Y Z : C) (W : D) (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: by
  rw [← Functor.map_comp]; rw [prod_comp]; rw [Category.comp_id]

@[simp]

中文:
定理 map_comp_id
  条件: (F : C × D ⥤ E) (X Y Z : C) (W : D) (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: by
  rw [← Functor.map_comp]; rw [prod_comp]; rw [Category.comp_id]

@[simp]

Depends on / 依赖: Category, Category.comp_id, Functor, Functor.map_comp, comp_id, map_comp, prod_comp
-/
theorem map_comp_id (F : C × D ⥤ E) (X Y Z : C) (W : D) (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map ((f ≫ g) ×ₘ 𝟙 W) = F.map (f ×ₘ 𝟙 W) ≫ F.map (g ×ₘ 𝟙 W) := by
  rw [← Functor.map_comp]; rw [prod_comp]; rw [Category.comp_id]

@[simp]
/--
theorem `diagonal` / 定理 `diagonal`

English:
theorem diagonal
  given: (F : C × D ⥤ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y')
  proof: by
  rw [← Functor.map_comp]; rw [prod_comp]; rw [Category.id_comp]; rw [Category.comp_id]

@[simp]

中文:
定理 diagonal
  条件: (F : C × D ⥤ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y')
  证明: by
  rw [← Functor.map_comp]; rw [prod_comp]; rw [Category.id_comp]; rw [Category.comp_id]

@[simp]

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, Functor, Functor.map_comp, comp_id, id_comp, map_comp, prod_comp
-/
theorem diagonal (F : C × D ⥤ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y') :
    F.map (𝟙 X ×ₘ g) ≫ F.map (f ×ₘ 𝟙 Y') = F.map (f ×ₘ g) := by
  rw [← Functor.map_comp]; rw [prod_comp]; rw [Category.id_comp]; rw [Category.comp_id]

@[simp]
/--
theorem `diagonal'` / 定理 `diagonal'`

English:
theorem diagonal'
  given: (F : C × D ⥤ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y')
  proof: by
  rw [← Functor.map_comp]; rw [prod_comp]; rw [Category.id_comp]; rw [Category.comp_id]

中文:
定理 diagonal'
  条件: (F : C × D ⥤ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y')
  证明: by
  rw [← Functor.map_comp]; rw [prod_comp]; rw [Category.id_comp]; rw [Category.comp_id]

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, Functor, Functor.map_comp, comp_id, id_comp, map_comp, prod_comp
-/
theorem diagonal' (F : C × D ⥤ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y') :
    F.map (f ×ₘ 𝟙 Y) ≫ F.map (𝟙 X' ×ₘ g) = F.map (f ×ₘ g) := by
  rw [← Functor.map_comp]; rw [prod_comp]; rw [Category.id_comp]; rw [Category.comp_id]

end CategoryTheory.Bifunctor
