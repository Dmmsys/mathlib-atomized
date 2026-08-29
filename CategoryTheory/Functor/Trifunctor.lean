/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.Category
/-!
# Trifunctors obtained by composition of bifunctors

Given two bifunctors `F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂` and `G : C₁₂ ⥤ C₃ ⥤ C₄`, we define
the trifunctor `bifunctorComp₁₂ F₁₂ G : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` which sends three
objects `X₁ : C₁`, `X₂ : C₂` and `X₃ : C₃` to `G.obj ((F₁₂.obj X₁).obj X₂).obj X₃`.

Similarly, given two bifunctors `F : C₁ ⥤ C₂₃ ⥤ C₄` and `G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃`, we define
the trifunctor `bifunctorComp₂₃ F G₂₃ : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` which sends three
objects `X₁ : C₁`, `X₂ : C₂` and `X₃ : C₃` to `(F.obj X₁).obj ((G₂₃.obj X₂).obj X₃)`.

-/

@[expose] public section

namespace CategoryTheory

variable {C₁ C₂ C₃ C₄ C₁₂ C₂₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* C₄] [Category* C₁₂] [Category* C₂₃]

section bifunctorComp₁₂Functor

/-- Auxiliary definition for `bifunctorComp₁₂`. -/
@[simps]
/--
Definition of `bifunctorComp₁₂Obj` / `bifunctorComp₁₂Obj` 的定义

English:
definition bifunctorComp₁₂Obj
  signature: (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) (G : C₁₂ ⥤ C₃ ⥤ C₄) (X₁ : C₁)
  body: { obj := fun X₃ => (G.obj ((F₁₂.obj X₁).obj X₂)).obj X₃
      map := fun {_ _} φ => (G.obj ((F₁₂.obj X₁).obj X₂)).map φ }
  map {X₂ Y₂} φ :=
    { app := fun X₃ => (G.map ((F₁₂.obj X₁).map φ)).app X₃ }

中文:
定义 bifunctorComp₁₂Obj
  签名: (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) (G : C₁₂ ⥤ C₃ ⥤ C₄) (X₁ : C₁)
  定义体: { obj := fun X₃ => (G.obj ((F₁₂.obj X₁).obj X₂)).obj X₃
      map := fun {_ _} φ => (G.obj ((F₁₂.obj X₁).obj X₂)).map φ }
  map {X₂ Y₂} φ :=
    { app := fun X₃ => (G.map ((F₁₂.obj X₁).map φ)).app X₃ }

Depends on / 依赖: G.map, G.obj
-/
def bifunctorComp₁₂Obj (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) (G : C₁₂ ⥤ C₃ ⥤ C₄) (X₁ : C₁) :
    C₂ ⥤ C₃ ⥤ C₄ where
  obj X₂ :=
    { obj := fun X₃ => (G.obj ((F₁₂.obj X₁).obj X₂)).obj X₃
      map := fun {_ _} φ => (G.obj ((F₁₂.obj X₁).obj X₂)).map φ }
  map {X₂ Y₂} φ :=
    { app := fun X₃ => (G.map ((F₁₂.obj X₁).map φ)).app X₃ }

set_option backward.defeqAttrib.useBackward true in
/-- Given two bifunctors `F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂` and `G : C₁₂ ⥤ C₃ ⥤ C₄`, this is
the trifunctor `C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` obtained by composition. -/
@[simps]
/--
Definition of `bifunctorComp₁₂` / `bifunctorComp₁₂` 的定义

English:
definition bifunctorComp₁₂
  signature: (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) (G : C₁₂ ⥤ C₃ ⥤ C₄)
  body: bifunctorComp₁₂Obj F₁₂ G X₁
  map {X₁ Y₁} φ :=
    { app := fun X₂ =>
        { app := fun X₃ => (G.map ((F₁₂.map φ).app X₂)).app X₃ }
      naturality := fun {X₂ Y₂} ψ => by
        ext X₃
        dsimp
        simp only [← NatTrans.comp_app, ← G.map_comp, NatTrans.naturality] }

中文:
定义 bifunctorComp₁₂
  签名: (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) (G : C₁₂ ⥤ C₃ ⥤ C₄)
  定义体: bifunctorComp₁₂Obj F₁₂ G X₁
  map {X₁ Y₁} φ :=
    { app := fun X₂ =>
        { app := fun X₃ => (G.map ((F₁₂.map φ).app X₂)).app X₃ }
      naturality := fun {X₂ Y₂} ψ => by
        ext X₃
        dsimp
        simp only [← NatTrans.comp_app, ← G.map_comp, NatTrans.naturality] }
-/
def bifunctorComp₁₂ (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) (G : C₁₂ ⥤ C₃ ⥤ C₄) :
    C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ where
  obj X₁ := bifunctorComp₁₂Obj F₁₂ G X₁
  map {X₁ Y₁} φ :=
    { app := fun X₂ =>
        { app := fun X₃ => (G.map ((F₁₂.map φ).app X₂)).app X₃ }
      naturality := fun {X₂ Y₂} ψ => by
        ext X₃
        dsimp
        simp only [← NatTrans.comp_app, ← G.map_comp, NatTrans.naturality] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `bifunctorComp₁₂Functor`. -/
@[simps]
/--
Definition of `bifunctorComp₁₂FunctorObj` / `bifunctorComp₁₂FunctorObj` 的定义

English:
definition bifunctorComp₁₂FunctorObj
  signature: (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂)
  body: bifunctorComp₁₂ F₁₂ G
  map {G G'} φ :=
    { app X₁ :=
        { app X₂ :=
            { app X₃ := (φ.app ((F₁₂.obj X₁).obj X₂)).app X₃ }
          naturality := fun X₂ Y₂ f => by
            ext X₃
            dsimp
            simp only [← NatTrans.comp_app, NatTrans.naturality] }
      naturality X₁ Y₁ f := by
        ext X₂ X₃
        dsimp
        simp only [← NatTrans.comp_app, NatTrans.naturality] }

中文:
定义 bifunctorComp₁₂FunctorObj
  签名: (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂)
  定义体: bifunctorComp₁₂ F₁₂ G
  map {G G'} φ :=
    { app X₁ :=
        { app X₂ :=
            { app X₃ := (φ.app ((F₁₂.obj X₁).obj X₂)).app X₃ }
          naturality := fun X₂ Y₂ f => by
            ext X₃
            dsimp
            simp only [← NatTrans.comp_app, NatTrans.naturality] }
      naturality X₁ Y₁ f := by
        ext X₂ X₃
        dsimp
        simp only [← NatTrans.comp_app, NatTrans.naturality] }
-/
def bifunctorComp₁₂FunctorObj (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) :
    (C₁₂ ⥤ C₃ ⥤ C₄) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ where
  obj G := bifunctorComp₁₂ F₁₂ G
  map {G G'} φ :=
    { app X₁ :=
        { app X₂ :=
            { app X₃ := (φ.app ((F₁₂.obj X₁).obj X₂)).app X₃ }
          naturality := fun X₂ Y₂ f => by
            ext X₃
            dsimp
            simp only [← NatTrans.comp_app, NatTrans.naturality] }
      naturality X₁ Y₁ f := by
        ext X₂ X₃
        dsimp
        simp only [← NatTrans.comp_app, NatTrans.naturality] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `bifunctorComp₁₂Functor`. -/
@[simps]
/--
Definition of `bifunctorComp₁₂FunctorMap` / `bifunctorComp₁₂FunctorMap` 的定义

English:
definition bifunctorComp₁₂FunctorMap
  signature: {F₁₂ F₁₂' : C₁ ⥤ C₂ ⥤ C₁₂} (φ : F₁₂ ⟶ F₁₂')
  body: { app X₁ :=
        { app X₂ := { app X₃ := (G.map ((φ.app X₁).app X₂)).app X₃ }
          naturality := fun X₂ Y₂ f => by
            ext X₃
            dsimp
            simp only [← NatTrans.comp_app, NatTrans.naturality, ← G.map_comp] }
      naturality X₁ Y₁ f := by
        ext X₂ X₃
        dsimp
        simp only [← NatTrans.comp_app, NatTrans.naturality, ← G.map_comp] }
  naturality G G' f := by
    ext X₁ X₂ X₃
    dsimp
    simp only [← NatTrans.comp_app, NatTrans.naturality]

中文:
定义 bifunctorComp₁₂FunctorMap
  签名: {F₁₂ F₁₂' : C₁ ⥤ C₂ ⥤ C₁₂} (φ : F₁₂ ⟶ F₁₂')
  定义体: { app X₁ :=
        { app X₂ := { app X₃ := (G.map ((φ.app X₁).app X₂)).app X₃ }
          naturality := fun X₂ Y₂ f => by
            ext X₃
            dsimp
            simp only [← NatTrans.comp_app, NatTrans.naturality, ← G.map_comp] }
      naturality X₁ Y₁ f := by
        ext X₂ X₃
        dsimp
        simp only [← NatTrans.comp_app, NatTrans.naturality, ← G.map_comp] }
  naturality G G' f := by
    ext X₁ X₂ X₃
    dsimp
    simp only [← NatTrans.comp_app, NatTrans.naturality]
-/
def bifunctorComp₁₂FunctorMap {F₁₂ F₁₂' : C₁ ⥤ C₂ ⥤ C₁₂} (φ : F₁₂ ⟶ F₁₂') :
    bifunctorComp₁₂FunctorObj (C₃ := C₃) (C₄ := C₄) F₁₂ ⟶ bifunctorComp₁₂FunctorObj F₁₂' where
  app G :=
    { app X₁ :=
        { app X₂ := { app X₃ := (G.map ((φ.app X₁).app X₂)).app X₃ }
          naturality := fun X₂ Y₂ f => by
            ext X₃
            dsimp
            simp only [← NatTrans.comp_app, NatTrans.naturality, ← G.map_comp] }
      naturality X₁ Y₁ f := by
        ext X₂ X₃
        dsimp
        simp only [← NatTrans.comp_app, NatTrans.naturality, ← G.map_comp] }
  naturality G G' f := by
    ext X₁ X₂ X₃
    dsimp
    simp only [← NatTrans.comp_app, NatTrans.naturality]

/-- The functor `(C₁ ⥤ C₂ ⥤ C₁₂) ⥤ (C₁₂ ⥤ C₃ ⥤ C₄) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` which
sends `F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂` and `G : C₁₂ ⥤ C₃ ⥤ C₄` to the functor
`bifunctorComp₁₂ F₁₂ G : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄`. -/
@[simps]
/--
Definition of `bifunctorComp₁₂Functor` / `bifunctorComp₁₂Functor` 的定义

English:
definition bifunctorComp₁₂Functor
  signature: : (C₁ ⥤ C₂ ⥤ C₁₂) ⥤ (C₁₂ ⥤ C₃ ⥤ C₄) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ where
  body: bifunctorComp₁₂FunctorObj
  map := bifunctorComp₁₂FunctorMap

中文:
定义 bifunctorComp₁₂Functor
  签名: : (C₁ ⥤ C₂ ⥤ C₁₂) ⥤ (C₁₂ ⥤ C₃ ⥤ C₄) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ where
  定义体: bifunctorComp₁₂FunctorObj
  map := bifunctorComp₁₂FunctorMap
-/
def bifunctorComp₁₂Functor : (C₁ ⥤ C₂ ⥤ C₁₂) ⥤ (C₁₂ ⥤ C₃ ⥤ C₄) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ where
  obj := bifunctorComp₁₂FunctorObj
  map := bifunctorComp₁₂FunctorMap

end bifunctorComp₁₂Functor

section bifunctorComp₂₃Functor

/-- Auxiliary definition for `bifunctorComp₂₃`. -/
@[simps]
/--
Definition of `bifunctorComp₂₃Obj` / `bifunctorComp₂₃Obj` 的定义

English:
definition bifunctorComp₂₃Obj
  signature: (F : C₁ ⥤ C₂₃ ⥤ C₄) (G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃) (X₁ : C₁)
  body: { obj X₃ := (F.obj X₁).obj ((G₂₃.obj X₂).obj X₃)
      map φ := (F.obj X₁).map ((G₂₃.obj X₂).map φ) }
  map {X₂ Y₂} φ :=
    { app X₃ := (F.obj X₁).map ((G₂₃.map φ).app X₃)
      naturality X₃ Y₃ φ := by
        dsimp
        simp only [← Functor.map_comp, NatTrans.naturality] }

中文:
定义 bifunctorComp₂₃Obj
  签名: (F : C₁ ⥤ C₂₃ ⥤ C₄) (G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃) (X₁ : C₁)
  定义体: { obj X₃ := (F.obj X₁).obj ((G₂₃.obj X₂).obj X₃)
      map φ := (F.obj X₁).map ((G₂₃.obj X₂).map φ) }
  map {X₂ Y₂} φ :=
    { app X₃ := (F.obj X₁).map ((G₂₃.map φ).app X₃)
      naturality X₃ Y₃ φ := by
        dsimp
        simp only [← Functor.map_comp, NatTrans.naturality] }

Depends on / 依赖: F.obj, Functor, Functor.map_comp, NatTrans, NatTrans.naturality, map_comp, naturality
-/
def bifunctorComp₂₃Obj (F : C₁ ⥤ C₂₃ ⥤ C₄) (G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃) (X₁ : C₁) :
    C₂ ⥤ C₃ ⥤ C₄ where
  obj X₂ :=
    { obj X₃ := (F.obj X₁).obj ((G₂₃.obj X₂).obj X₃)
      map φ := (F.obj X₁).map ((G₂₃.obj X₂).map φ) }
  map {X₂ Y₂} φ :=
    { app X₃ := (F.obj X₁).map ((G₂₃.map φ).app X₃)
      naturality X₃ Y₃ φ := by
        dsimp
        simp only [← Functor.map_comp, NatTrans.naturality] }

set_option backward.defeqAttrib.useBackward true in
/-- Given two bifunctors `F : C₁ ⥤ C₂₃ ⥤ C₄` and `G₂₃ : C₂ ⥤ C₃ ⥤ C₄`, this is
the trifunctor `C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` obtained by composition. -/
@[simps]
/--
Definition of `bifunctorComp₂₃` / `bifunctorComp₂₃` 的定义

English:
definition bifunctorComp₂₃
  signature: (F : C₁ ⥤ C₂₃ ⥤ C₄) (G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃)
  body: bifunctorComp₂₃Obj F G₂₃ X₁
  map {X₁ Y₁} φ :=
    { app := fun X₂ =>
        { app := fun X₃ => (F.map φ).app ((G₂₃.obj X₂).obj X₃) } }

中文:
定义 bifunctorComp₂₃
  签名: (F : C₁ ⥤ C₂₃ ⥤ C₄) (G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃)
  定义体: bifunctorComp₂₃Obj F G₂₃ X₁
  map {X₁ Y₁} φ :=
    { app := fun X₂ =>
        { app := fun X₃ => (F.map φ).app ((G₂₃.obj X₂).obj X₃) } }
-/
def bifunctorComp₂₃ (F : C₁ ⥤ C₂₃ ⥤ C₄) (G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃) :
    C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ where
  obj X₁ := bifunctorComp₂₃Obj F G₂₃ X₁
  map {X₁ Y₁} φ :=
    { app := fun X₂ =>
        { app := fun X₃ => (F.map φ).app ((G₂₃.obj X₂).obj X₃) } }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `bifunctorComp₂₃Functor`. -/
@[simps]
/--
Definition of `bifunctorComp₂₃FunctorObj` / `bifunctorComp₂₃FunctorObj` 的定义

English:
definition bifunctorComp₂₃FunctorObj
  signature: (F : C₁ ⥤ C₂₃ ⥤ C₄)
  body: bifunctorComp₂₃ F G₂₃
  map {G₂₃ G₂₃'} φ :=
    { app X₁ :=
        { app X₂ :=
            { app X₃ := (F.obj X₁).map ((φ.app X₂).app X₃)
              naturality X₃ Y₃ f := by
                dsimp
                simp only [← Functor.map_comp, NatTrans.naturality] }
          naturality X₂ Y₂ f := by
            ext X₃
            dsimp
            simp only [← NatTrans.comp_app, ← Functor.map_comp, NatTrans.naturality] } }

中文:
定义 bifunctorComp₂₃FunctorObj
  签名: (F : C₁ ⥤ C₂₃ ⥤ C₄)
  定义体: bifunctorComp₂₃ F G₂₃
  map {G₂₃ G₂₃'} φ :=
    { app X₁ :=
        { app X₂ :=
            { app X₃ := (F.obj X₁).map ((φ.app X₂).app X₃)
              naturality X₃ Y₃ f := by
                dsimp
                simp only [← Functor.map_comp, NatTrans.naturality] }
          naturality X₂ Y₂ f := by
            ext X₃
            dsimp
            simp only [← NatTrans.comp_app, ← Functor.map_comp, NatTrans.naturality] } }
-/
def bifunctorComp₂₃FunctorObj (F : C₁ ⥤ C₂₃ ⥤ C₄) :
    (C₂ ⥤ C₃ ⥤ C₂₃) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ where
  obj G₂₃ := bifunctorComp₂₃ F G₂₃
  map {G₂₃ G₂₃'} φ :=
    { app X₁ :=
        { app X₂ :=
            { app X₃ := (F.obj X₁).map ((φ.app X₂).app X₃)
              naturality X₃ Y₃ f := by
                dsimp
                simp only [← Functor.map_comp, NatTrans.naturality] }
          naturality X₂ Y₂ f := by
            ext X₃
            dsimp
            simp only [← NatTrans.comp_app, ← Functor.map_comp, NatTrans.naturality] } }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `bifunctorComp₂₃Functor`. -/
@[simps]
/--
Definition of `bifunctorComp₂₃FunctorMap` / `bifunctorComp₂₃FunctorMap` 的定义

English:
definition bifunctorComp₂₃FunctorMap
  signature: {F F' : C₁ ⥤ C₂₃ ⥤ C₄} (φ : F ⟶ F')
  body: { app X₁ := { app X₂ := { app X₃ := (φ.app X₁).app ((G₂₃.obj X₂).obj X₃) } }
      naturality X₁ Y₁ f := by
        ext X₂ X₃
        dsimp
        simp only [← NatTrans.comp_app, NatTrans.naturality] }

中文:
定义 bifunctorComp₂₃FunctorMap
  签名: {F F' : C₁ ⥤ C₂₃ ⥤ C₄} (φ : F ⟶ F')
  定义体: { app X₁ := { app X₂ := { app X₃ := (φ.app X₁).app ((G₂₃.obj X₂).obj X₃) } }
      naturality X₁ Y₁ f := by
        ext X₂ X₃
        dsimp
        simp only [← NatTrans.comp_app, NatTrans.naturality] }
-/
def bifunctorComp₂₃FunctorMap {F F' : C₁ ⥤ C₂₃ ⥤ C₄} (φ : F ⟶ F') :
    bifunctorComp₂₃FunctorObj F (C₂ := C₂) (C₃ := C₃) ⟶ bifunctorComp₂₃FunctorObj F' where
  app G₂₃ :=
    { app X₁ := { app X₂ := { app X₃ := (φ.app X₁).app ((G₂₃.obj X₂).obj X₃) } }
      naturality X₁ Y₁ f := by
        ext X₂ X₃
        dsimp
        simp only [← NatTrans.comp_app, NatTrans.naturality] }

/-- The functor `(C₁ ⥤ C₂₃ ⥤ C₄) ⥤ (C₂ ⥤ C₃ ⥤ C₂₃) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` which
sends `F : C₁ ⥤ C₂₃ ⥤ C₄` and `G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃` to the
functor `bifunctorComp₂₃ F G₂₃ : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄`. -/
@[simps]
/--
Definition of `bifunctorComp₂₃Functor` / `bifunctorComp₂₃Functor` 的定义

English:
definition bifunctorComp₂₃Functor
  signature: :
  body: bifunctorComp₂₃FunctorObj
  map := bifunctorComp₂₃FunctorMap

中文:
定义 bifunctorComp₂₃Functor
  签名: :
  定义体: bifunctorComp₂₃FunctorObj
  map := bifunctorComp₂₃FunctorMap
-/
def bifunctorComp₂₃Functor :
    (C₁ ⥤ C₂₃ ⥤ C₄) ⥤ (C₂ ⥤ C₃ ⥤ C₂₃) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ where
  obj := bifunctorComp₂₃FunctorObj
  map := bifunctorComp₂₃FunctorMap

end bifunctorComp₂₃Functor

end CategoryTheory
