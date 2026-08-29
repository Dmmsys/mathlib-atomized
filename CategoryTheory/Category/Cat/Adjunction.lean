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
/--
Definition of `typeToCatObjectsAdjHomEquiv` / `typeToCatObjectsAdjHomEquiv` 的定义

English:
definition typeToCatObjectsAdjHomEquiv
  signature: : (typeToCat.obj X ⟶ C) ≃ (X ⟶ Cat.objects.obj C) where
  body: ↾fun x => F.toFunctor.obj ⟨x⟩
  invFun f := (Discrete.functor f).toCatHom
left_inv F := Hom.ext Functor.ext (fun _ => rfl) (fun ⟨_⟩ ⟨_⟩ f => by
    obtain rfl := Discrete.eq_of_hom f
    simp)

中文:
定义 typeToCatObjectsAdjHomEquiv
  签名: : (typeToCat.obj X ⟶ C) ≃ (X ⟶ Cat.objects.obj C) where
  定义体: ↾fun x => F.toFunctor.obj ⟨x⟩
  invFun f := (Discrete.functor f).toCatHom
left_inv F := Hom.ext Functor.ext (fun _ => rfl) (fun ⟨_⟩ ⟨_⟩ f => by
    obtain rfl := Discrete.eq_of_hom f
    simp)
-/
private def typeToCatObjectsAdjHomEquiv : (typeToCat.obj X ⟶ C) ≃ (X ⟶ Cat.objects.obj C) where
  toFun F := ↾fun x => F.toFunctor.obj ⟨x⟩
  invFun f := (Discrete.functor f).toCatHom
left_inv F := Hom.ext Functor.ext (fun _ => rfl) (fun ⟨_⟩ ⟨_⟩ f => by
    obtain rfl := Discrete.eq_of_hom f
    simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
/--
Definition of `typeToCatObjectsAdjCounitApp` / `typeToCatObjectsAdjCounitApp` 的定义

English:
definition typeToCatObjectsAdjCounitApp
  signature: : (Cat.objects ⋙ typeToCat).obj C ⥤ C where
  body: Discrete.as
  map := eqToHom ∘ Discrete.eq_of_hom

中文:
定义 typeToCatObjectsAdjCounitApp
  签名: : (Cat.objects ⋙ typeToCat).obj C ⥤ C where
  定义体: Discrete.as
  map := eqToHom ∘ Discrete.eq_of_hom
-/
private def typeToCatObjectsAdjCounitApp : (Cat.objects ⋙ typeToCat).obj C ⥤ C where
  obj := Discrete.as
  map := eqToHom ∘ Discrete.eq_of_hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `typeToCatObjectsAdj` / `typeToCatObjectsAdj` 的定义

English:
definition typeToCatObjectsAdj
  signature: : typeToCat ⊣ Cat.objects
  body: Adjunction.mk' {
    homEquiv := typeToCatObjectsAdjHomEquiv
    unit := { app := fun _ => ↾Discrete.mk }
    counit := {
      app C := (typeToCatObjectsAdjCounitApp C).toCatHom
naturality := fun _ _ _ => Hom.ext Functor.hext (fun _ => rfl)
        (by intro ⟨_⟩ ⟨_⟩ f
            obtain rfl := Disc

中文:
定义 typeToCatObjectsAdj
  签名: : typeToCat ⊣ Cat.objects
  定义体: Adjunction.mk' {
    homEquiv := typeToCatObjectsAdjHomEquiv
    unit := { app := fun _ => ↾Discrete.mk }
    counit := {
      app C := (typeToCatObjectsAdjCounitApp C).toCatHom
naturality := fun _ _ _ => Hom.ext Functor.hext (fun _ => rfl)
        (by intro ⟨_⟩ ⟨_⟩ f
            obtain rfl := Disc

Depends on / 依赖: Adjunction, Adjunction.mk, Discrete, Discrete.eq_of_hom, Discrete.mk, Functor, Functor.hext, Hom.ext, cat_disch, counit, eq_of_hom, homEquiv, naturality, toCatHom, typeToCatObjectsAdjCounitApp, typeToCatObjectsAdjHomEquiv
-/
def typeToCatObjectsAdj : typeToCat ⊣ Cat.objects :=
  Adjunction.mk' {
    homEquiv := typeToCatObjectsAdjHomEquiv
    unit := { app := fun _ => ↾Discrete.mk }
    counit := {
      app C := (typeToCatObjectsAdjCounitApp C).toCatHom
naturality := fun _ _ _ => Hom.ext Functor.hext (fun _ => rfl)
        (by intro ⟨_⟩ ⟨_⟩ f
            obtain rfl := Discrete.eq_of_hom f
            cat_disch) } }

/--
Definition of `connectedComponents` / `connectedComponents` 的定义

English:
definition connectedComponents
  signature: : Cat.{v, u} ⥤ Type u where
  body: ConnectedComponents C
  map F := ↾(Functor.mapConnectedComponents F.toFunctor)
  map_id _ := by ext x; simpa using (Quotient.exists_rep x).elim (fun _ h => by subst h; rfl)
  map_comp _ _ := by ext x; simpa using (Quotient.exists_rep x).elim (fun _ h => by subst h; rfl)

中文:
定义 connectedComponents
  签名: : Cat.{v, u} ⥤ 类型u where
  定义体: ConnectedComponents C
  map F := ↾(Functor.mapConnectedComponents F.toFunctor)
  map_id _ := by ext x; simpa using (Quotient.exists_rep x).elim (fun _ h => by subst h; rfl)
  map_comp _ _ := by ext x; simpa using (Quotient.exists_rep x).elim (fun _ h => by subst h; rfl)

Depends on / 依赖: ConnectedComponents
-/
def connectedComponents : Cat.{v, u} ⥤ Type u where
  obj C := ConnectedComponents C
  map F := ↾(Functor.mapConnectedComponents F.toFunctor)
  map_id _ := by ext x; simpa using (Quotient.exists_rep x).elim (fun _ h => by subst h; rfl)
  map_comp _ _ := by ext x; simpa using (Quotient.exists_rep x).elim (fun _ h => by subst h; rfl)

/--
Definition of `connectedComponentsTypeToCatAdj` / `connectedComponentsTypeToCatAdj` 的定义

English:
definition connectedComponentsTypeToCatAdj
  signature: : connectedComponents.{u} ⊣ typeToCat.{u}
  body: Adjunction.mk' {
    homEquiv := fun C X => by
      refine TypeCat.homEquiv.trans ?_
      exact (ConnectedComponents.typeToCatHomEquiv _ _).trans
        (Functor.equivCatHom _ _)
    unit :=
      { app := fun C => Functor.toCatHom <|
          ConnectedComponents.functorToDiscrete _ (𝟙 (connecte

中文:
定义 connectedComponentsTypeToCatAdj
  签名: : connectedComponents.{u} ⊣ typeToCat.{u}
  定义体: Adjunction.mk' {
    homEquiv := fun C X => by
      refine TypeCat.homEquiv.trans ?_
      exact (ConnectedComponents.typeToCatHomEquiv _ _).trans
        (Functor.equivCatHom _ _)
    unit :=
      { app := fun C => Functor.toCatHom <|
          ConnectedComponents.functorToDiscrete _ (𝟙 (connecte

Depends on / 依赖: Adjunction, Adjunction.mk, ConnectedComponents, ConnectedComponents.functorToDiscrete, ConnectedComponents.liftFunctor, ConnectedComponents.typeToCatHomEquiv, Functor, Functor.equivCatHom, Functor.toCatHom, Quotient, Quotient.exists_rep, TypeCat, TypeCat.homEquiv.trans, cat_disch, connectedComponents, connectedComponents.obj, counit, equivCatHom, exists_rep, functorToDiscrete
-/
def connectedComponentsTypeToCatAdj : connectedComponents.{u} ⊣ typeToCat.{u} :=
  Adjunction.mk' {
    homEquiv := fun C X => by
      refine TypeCat.homEquiv.trans ?_
      exact (ConnectedComponents.typeToCatHomEquiv _ _).trans
        (Functor.equivCatHom _ _)
    unit :=
      { app := fun C => Functor.toCatHom <|
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
