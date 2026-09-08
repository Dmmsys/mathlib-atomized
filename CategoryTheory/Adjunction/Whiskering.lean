/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!

Given categories `C D E`, functors `F : D ⥤ E` and `G : E ⥤ D` with an adjunction
`F ⊣ G`, we provide the induced adjunction between the functor categories `C ⥤ D` and `C ⥤ E`,
and the functor categories `E ⥤ C` and `D ⥤ C`.

-/

@[expose] public section


namespace CategoryTheory.Adjunction

open CategoryTheory CategoryTheory.Functor

variable (C : Type*) {D E : Type*} [Category* C] [Category* D] [Category* E] {F : D ⥤ E} {G : E ⥤ D}

set_option backward.defeqAttrib.useBackward true in
/-- Given an adjunction `F ⊣ G`, this provides the natural adjunction
  `(whiskeringRight C _ _).obj F ⊣ (whiskeringRight C _ _).obj G`. -/
@[simps! unit_app_app counit_app_app]
/-
**CategoryTheory.Adjunction.whiskerRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Adjunction`。
形式化陈述：(C : Type u_1) →   {D : Type u_2} →     {E : Type u_3} →       [inst : Cat
egoryTheory.Category.{v_1, u_1} C] →         [inst_1 : CategoryTheory.Category.{
v_2, u_2} D] →           [inst_2 : CategoryTheory.Category.{v_3, u_3} E] →      
       {F : CategoryTheory.Functor D E} →               {G : CategoryTheory.Func
tor E D} →                 (F ⊣ G) →                   ((CategoryTheory.Functor.
whiskeringRight C D E).obj F ⊣                     (CategoryTheory.Functor.whisk
eringRight C E D).obj G)
参数：CategoryTheory.Functor.whiskeringRight C D E；CategoryTheory.Functor.whiskerin
gRight C E D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an adjunction `F ⊣ G`, this provides the natural adjunction
  `(whiskeringRight C _ _).obj F ⊣ (whiskeringRight C _ _).obj G`.
-/
protected def whiskerRight (adj : F ⊣ G) :
    (whiskeringRight C D E).obj F ⊣ (whiskeringRight C E D).obj G where
  unit :=
    { app := fun X =>
        (rightUnitor _).inv ≫ whiskerLeft X adj.unit ≫ (associator _ _ _).inv
      naturality := by intros; ext; simp }
  counit :=
    { app := fun X =>
        (associator _ _ _).hom ≫ whiskerLeft X adj.counit ≫ (rightUnitor _).hom
      naturality := by intros; ext; simp }

set_option backward.defeqAttrib.useBackward true in
/-- Given an adjunction `F ⊣ G`, this provides the natural adjunction
  `(whiskeringLeft _ _ C).obj G ⊣ (whiskeringLeft _ _ C).obj F`. -/
@[simps! unit_app_app counit_app_app]
/-
**CategoryTheory.Adjunction.whiskerLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Adjunction`。
形式化陈述：(C : Type u_1) →   {D : Type u_2} →     {E : Type u_3} →       [inst : Cat
egoryTheory.Category.{v_1, u_1} C] →         [inst_1 : CategoryTheory.Category.{
v_2, u_2} D] →           [inst_2 : CategoryTheory.Category.{v_3, u_3} E] →      
       {F : CategoryTheory.Functor D E} →               {G : CategoryTheory.Func
tor E D} →                 (F ⊣ G) →                   ((CategoryTheory.Functor.
whiskeringLeft E D C).obj G ⊣                     (CategoryTheory.Functor.whiske
ringLeft D E C).obj F)
参数：CategoryTheory.Functor.whiskeringLeft E D C；CategoryTheory.Functor.whiskering
Left D E C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an adjunction `F ⊣ G`, this provides the natural adjunction
  `(whiskeringLeft _ _ C).obj G ⊣ (whiskeringLeft _ _ C).obj F`.
-/
protected def whiskerLeft (adj : F ⊣ G) :
    (whiskeringLeft E D C).obj G ⊣ (whiskeringLeft D E C).obj F where
  unit :=
    { app := fun X =>
        (leftUnitor _).inv ≫ whiskerRight adj.unit X ≫ (associator _ _ _).hom }
  counit :=
    { app := fun X =>
        (associator _ _ _).inv ≫ whiskerRight adj.counit X ≫ (leftUnitor _).hom }
  left_triangle_components X := by ext; simp [← X.map_comp]
  right_triangle_components X := by ext; simp [← X.map_comp]

end CategoryTheory.Adjunction

