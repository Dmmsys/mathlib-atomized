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
/-
**CategoryTheory.Bifunctor.map_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Bifu
nctor`。
形式化陈述：map_id (F : C × D ⥤ E) (X : C) (Y : D) : F.map ((𝟙 X) ×ₘ (𝟙 Y)) = 𝟙 (F.obj
 (X, Y))
参数：F : C × D ⥤ E；X : C；Y : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
theorem map_id (F : C × D ⥤ E) (X : C) (Y : D) :
    F.map ((𝟙 X) ×ₘ (𝟙 Y)) = 𝟙 (F.obj (X, Y)) :=
  F.map_id (X, Y)

@[simp]
/-
**CategoryTheory.Bifunctor.map_id_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Bifunctor`。
形式化陈述：map_id_comp (F : C × D ⥤ E) (W : C) {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) : 
F.map (𝟙 W ×ₘ (f ≫ g)) = F.map (𝟙 W ×ₘ f) ≫ F.map (𝟙 W ×ₘ g)
参数：F : C × D ⥤ E；W : C；f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.prod_comp`：prod_comp {P Q R : C} {S T U : D} (f : (P, S) 
⟶ (Q, T)) (g : (Q, T) ⟶ (R, U)) : f ≫ g = f.1 ≫ g.1 ×ₘ f.2 ≫ g.2
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem map_id_comp (F : C × D ⥤ E) (W : C) {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (𝟙 W ×ₘ (f ≫ g)) = F.map (𝟙 W ×ₘ f) ≫ F.map (𝟙 W ×ₘ g) := by
  rw [← Functor.map_comp, prod_comp, Category.comp_id]

@[simp]
/-
**CategoryTheory.Bifunctor.map_comp_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Bifunctor`。
形式化陈述：map_comp_id (F : C × D ⥤ E) (X Y Z : C) (W : D) (f : X ⟶ Y) (g : Y ⟶ Z) : 
F.map ((f ≫ g) ×ₘ 𝟙 W) = F.map (f ×ₘ 𝟙 W) ≫ F.map (g ×ₘ 𝟙 W)
参数：F : C × D ⥤ E；X Y Z : C；W : D；f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.prod_comp`：prod_comp {P Q R : C} {S T U : D} (f : (P, S) 
⟶ (Q, T)) (g : (Q, T) ⟶ (R, U)) : f ≫ g = f.1 ≫ g.1 ×ₘ f.2 ≫ g.2
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem map_comp_id (F : C × D ⥤ E) (X Y Z : C) (W : D) (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map ((f ≫ g) ×ₘ 𝟙 W) = F.map (f ×ₘ 𝟙 W) ≫ F.map (g ×ₘ 𝟙 W) := by
  rw [← Functor.map_comp, prod_comp, Category.comp_id]

@[simp]
/-
**CategoryTheory.Bifunctor.diagonal** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Bi
functor`。
形式化陈述：diagonal (F : C × D ⥤ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y') :
 F.map (𝟙 X ×ₘ g) ≫ F.map (f ×ₘ 𝟙 Y') = F.map (f ×ₘ g)
参数：F : C × D ⥤ E；X X' : C；f : X ⟶ X'；Y Y' : D；g : Y ⟶ Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.prod_comp`：prod_comp {P Q R : C} {S T U : D} (f : (P, S) 
⟶ (Q, T)) (g : (Q, T) ⟶ (R, U)) : f ≫ g = f.1 ≫ g.1 ×ₘ f.2 ≫ g.2
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem diagonal (F : C × D ⥤ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y') :
    F.map (𝟙 X ×ₘ g) ≫ F.map (f ×ₘ 𝟙 Y') = F.map (f ×ₘ g) := by
  rw [← Functor.map_comp, prod_comp, Category.id_comp, Category.comp_id]

@[simp]
/-
**CategoryTheory.Bifunctor.diagonal'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.B
ifunctor`。
形式化陈述：diagonal' (F : C × D ⥤ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y') 
: F.map (f ×ₘ 𝟙 Y) ≫ F.map (𝟙 X' ×ₘ g) = F.map (f ×ₘ g)
参数：F : C × D ⥤ E；X X' : C；f : X ⟶ X'；Y Y' : D；g : Y ⟶ Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.prod_comp`：prod_comp {P Q R : C} {S T U : D} (f : (P, S) 
⟶ (Q, T)) (g : (Q, T) ⟶ (R, U)) : f ≫ g = f.1 ≫ g.1 ×ₘ f.2 ≫ g.2
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem diagonal' (F : C × D ⥤ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y') :
    F.map (f ×ₘ 𝟙 Y) ≫ F.map (𝟙 X' ×ₘ g) = F.map (f ×ₘ g) := by
  rw [← Functor.map_comp, prod_comp, Category.id_comp, Category.comp_id]

end CategoryTheory.Bifunctor

