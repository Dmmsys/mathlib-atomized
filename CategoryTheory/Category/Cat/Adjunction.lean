/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.ConnectedComponents

/-!
# Adjunctions related to Cat, the category of categories

The embedding `typeToCat: Type ⥤ Cat`, mapping a type to the corresponding discrete category, is
left adjoint to the functor `Cat.objects`, which maps a category to its set of objects.

Another functor `connectedComponents : Cat ⥤ Type` maps a category to the set of its connected
components and functors to functions between those sets.

## Notes
All this could be made with 2-functors

-/

@[expose] public section

universe v u
namespace CategoryTheory.Cat

variable (X : Type u) (C : Cat)

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
/-
**CategoryTheory.Cat.typeToCatObjectsAdjHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Cat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def typeToCatObjectsAdjHomEquiv : (typeToCat.obj X ⟶ C) ≃ (X ⟶ Cat.objects.obj C) where
  toFun F := ↾fun x ↦ F.toFunctor.obj ⟨x⟩
  invFun f := (Discrete.functor f).toCatHom
  left_inv F := Hom.ext <| Functor.ext (fun _ ↦ rfl) (fun ⟨_⟩ ⟨_⟩ f => by
    obtain rfl := Discrete.eq_of_hom f
    simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
/-
**CategoryTheory.Cat.typeToCatObjectsAdjCounitApp** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Cat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def typeToCatObjectsAdjCounitApp : (Cat.objects ⋙ typeToCat).obj C ⥤ C where
  obj := Discrete.as
  map := eqToHom ∘ Discrete.eq_of_hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- `typeToCat : Type ⥤ Cat` is left adjoint to `Cat.objects : Cat ⥤ Type` -/
/-
**CategoryTheory.Cat.typeToCatObjectsAdj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Cat`。
形式化陈述：typeToCatObjectsAdj : typeToCat ⊣ Cat.objects
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`typeToCat : Type ⥤ Cat` is left adjoint to `Cat.objects : Cat ⥤ Type`
-/
def typeToCatObjectsAdj : typeToCat ⊣ Cat.objects :=
  Adjunction.mk' {
    homEquiv := typeToCatObjectsAdjHomEquiv
    unit := { app := fun _ ↦ ↾Discrete.mk }
    counit := {
      app C := (typeToCatObjectsAdjCounitApp C).toCatHom
      naturality := fun _ _ _ ↦ Hom.ext <| Functor.hext (fun _ ↦ rfl)
        (by intro ⟨_⟩ ⟨_⟩ f
            obtain rfl := Discrete.eq_of_hom f
            cat_disch) } }

/-- The connected components functor -/
/-
**CategoryTheory.Cat.connectedComponents** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Cat`。
形式化陈述：connectedComponents : Cat.{v, u} ⥤ Type u where obj C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The connected components functor
-/
def connectedComponents : Cat.{v, u} ⥤ Type u where
  obj C := ConnectedComponents C
  map F := ↾(Functor.mapConnectedComponents F.toFunctor)
  map_id _ := by ext x; simpa using (Quotient.exists_rep x).elim (fun _ h ↦ by subst h; rfl)
  map_comp _ _ := by ext x; simpa using (Quotient.exists_rep x).elim (fun _ h => by subst h; rfl)

/-- `typeToCat : Type ⥤ Cat` is right adjoint to `connectedComponents : Cat ⥤ Type` -/
/-
**CategoryTheory.Cat.connectedComponentsTypeToCatAdj** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Cat`。
形式化陈述：connectedComponentsTypeToCatAdj : connectedComponents.{u} ⊣ typeToCat.{u}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
`typeToCat : Type ⥤ Cat` is right adjoint to `connectedComponents : Cat ⥤ Type`
-/
def connectedComponentsTypeToCatAdj : connectedComponents.{u} ⊣ typeToCat.{u} :=
  Adjunction.mk' {
    homEquiv := fun C X ↦ by
      refine TypeCat.homEquiv.trans ?_
      exact (ConnectedComponents.typeToCatHomEquiv _ _).trans
        (Functor.equivCatHom _ _)
    unit :=
      { app := fun C ↦ Functor.toCatHom <|
          ConnectedComponents.functorToDiscrete _ (𝟙 (connectedComponents.obj C)) }
    counit := {
        app := fun X => ↾(ConnectedComponents.liftFunctor _
          (𝟙 typeToCat.obj X).toFunctor)
        naturality := fun _ _ _ => by
          ext xcc
          obtain ⟨x, h⟩ := Quotient.exists_rep xcc
          cat_disch }
    homEquiv_counit := fun {C X G} => by
      ext cc
      obtain ⟨_, _⟩ := Quotient.exists_rep cc
      cat_disch }

end CategoryTheory.Cat

