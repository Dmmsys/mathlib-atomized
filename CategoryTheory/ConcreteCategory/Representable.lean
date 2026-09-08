/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.ConcreteCategory.Forget

/-!

# Representable functors in concrete categories

This file provides some API for the situation `(F ⋙ forget D).RepresentableBy Y`.
-/

@[expose] public section

namespace CategoryTheory.Functor.RepresentableBy

open Opposite

variable {C D : Type*} [Category* C] [Category* D] {F : Cᵒᵖ ⥤ D}
    {CD : D → Type*} {FD : D → D → Type*} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory D FD] {Y : C} (α : (F ⋙ forget D).RepresentableBy Y)

/-- The natural bijection `(X ⟶ Y) ≃ F.obj (op X)`. -/
/-
**CategoryTheory.Functor.RepresentableBy.homEquiv'** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Functor.RepresentableBy`。
形式化陈述：homEquiv' {X : C} : (X ⟶ Y) ≃ ToType (F.obj (op X))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural bijection `(X ⟶ Y) ≃ F.obj (op X)`.
-/
def homEquiv' {X : C} : (X ⟶ Y) ≃ ToType (F.obj (op X)) := α.homEquiv
/-
**CategoryTheory.Functor.RepresentableBy.homEquiv'_comp** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Functor.RepresentableBy`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {F : CategoryTheory.Functo
r Cᵒᵖ D} {CD : D → Type u_3}   {FD : D → D → Type u_4} [inst_2 : (X Y : D) → Fun
Like (FD X Y) (CD X) (CD Y)]   [inst_3 : CategoryTheory.ConcreteCategory D FD] {
Y : C} (α : (F.comp (CategoryTheory.forget D)).RepresentableBy Y)   {X X' : C} (
f : X ⟶ X') (g : X' ⟶ Y),   α.homEquiv' (CategoryTheory.CategoryStruct.comp f g)
 =     (CategoryTheory.ConcreteCategory.hom (F.map f.op)) (α.homEquiv' g)
参数：X Y : D；FD X Y；CD X；CD Y；α : (F.comp (CategoryTheory.forget D)).Representable
By Y；f : X ⟶ X'；g : X' ⟶ Y；CategoryTheory.CategoryStruct.comp f g；CategoryTheory
.ConcreteCategory.hom (F.map f.op)；α.homEquiv' g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.RepresentableBy.homEquiv_comp`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor Cᵒᵖ (Type 
v)} {Y : C}   (self : F.RepresentableBy Y)…
-/
lemma homEquiv'_comp {X X' : C} (f : X ⟶ X') (g : X' ⟶ Y) :
    α.homEquiv' (f ≫ g) = F.map f.op (α.homEquiv' g) := α.homEquiv_comp _ _

end CategoryTheory.Functor.RepresentableBy

