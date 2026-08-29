/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

/-!
# Pseudofunctors from locally discrete bicategories

This file provides various ways of constructing pseudofunctors from locally discrete
bicategories.

Firstly, we define the constructors `pseudofunctorOfIsLocallyDiscrete` and
`oplaxFunctorOfIsLocallyDiscrete` for defining pseudofunctors and oplax functors
from a locally discrete bicategory. In this situation, we do not need to care about
the field `map₂`, because all the `2`-morphisms in `B` are identities.

We also define a specialized constructor `LocallyDiscrete.mkPseudofunctor` when
the source bicategory is of the form `B := LocallyDiscrete B₀` for a category `B₀`.

We also prove that a functor `F : I ⥤ B` with `B` a strict bicategory can be promoted
to a pseudofunctor (or oplax functor) (`Functor.toPseudofunctor`) with domain
`LocallyDiscrete I`.

-/

@[expose] public section

namespace CategoryTheory

open Bicategory

/-- Constructor for pseudofunctors from a locally discrete bicategory. In that
case, we do not need to provide the `map₂` field of pseudofunctors. -/
@[simps obj map mapId mapComp]
/--
Definition of `pseudofunctorOfIsLocallyDiscrete` / `pseudofunctorOfIsLocallyDiscrete` 的定义

English:
definition pseudofunctorOfIsLocallyDiscrete
  body: obj
  map := map
  map₂ φ := eqToHom (by
    obtain rfl := obj_ext_of_isDiscrete φ
    dsimp)
  mapId := mapId
  mapComp := mapComp
  map₂_whisker_left _ _ _ η := by
    obtain rfl := obj_ext_of_isDiscrete η
    simp
  map₂_whisker_right η _ := by
    obtain rfl := obj_ext_of_isDiscrete η
    simp

中文:
定义 pseudofunctorOfIsLocallyDiscrete
  定义体: obj
  map := map
  map₂ φ := eqToHom (by
    obtain rfl := obj_ext_of_isDiscrete φ
    dsimp)
  mapId := mapId
  mapComp := mapComp
  map₂_whisker_left _ _ _ η := by
    obtain rfl := obj_ext_of_isDiscrete η
    simp
  map₂_whisker_right η _ := by
    obtain rfl := obj_ext_of_isDiscrete η
    simp

Depends on / 依赖: cat_disch, eqToHom, fun_, mapComp, obj_ext_of_isDiscrete
-/
def pseudofunctorOfIsLocallyDiscrete
    {B C : Type*} [Bicategory B] [IsLocallyDiscrete B] [Bicategory C]
    (obj : B -> C)
    (map : forall {b b' : B}, (b ⟶ b') -> (obj b ⟶ obj b'))
    (mapId : forall (b : B), map (𝟙 b) ≅ 𝟙 _)
    (mapComp : forall {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂), map (f ≫ g) ≅ map f ≫ map g)
    (map₂_associator : forall {b₀ b₁ b₂ b₃ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃),
      (mapComp (f ≫ g) h).hom ≫
        (mapComp f g).hom ▷ map h ≫ (α_ (map f) (map g) (map h)).hom ≫
          map f ◁ (mapComp g h).inv ≫ (mapComp f (g ≫ h)).inv = eqToHom (by simp) := by cat_disch)
    (map₂_left_unitor : forall {b₀ b₁ : B} (f : b₀ ⟶ b₁),
      (mapComp (𝟙 b₀) f).hom ≫ (mapId b₀).hom ▷ map f ≫ (fun_ (map f)).hom = eqToHom (by simp) := by
        cat_disch)
    (map₂_right_unitor : forall {b₀ b₁ : B} (f : b₀ ⟶ b₁),
      (mapComp f (𝟙 b₁)).hom ≫ map f ◁ (mapId b₁).hom ≫ (ρ_ (map f)).hom = eqToHom (by simp) := by
        cat_disch) :
    B ⥤ᵖ C where
  obj := obj
  map := map
  map₂ φ := eqToHom (by
    obtain rfl := obj_ext_of_isDiscrete φ
    dsimp)
  mapId := mapId
  mapComp := mapComp
  map₂_whisker_left _ _ _ η := by
    obtain rfl := obj_ext_of_isDiscrete η
    simp
  map₂_whisker_right η _ := by
    obtain rfl := obj_ext_of_isDiscrete η
    simp

/-- Constructor for oplax functors from a locally discrete bicategory. In that
case, we do not need to provide the `map₂` field of oplax functors. -/
@[simps obj map mapId mapComp]
/--
Definition of `oplaxFunctorOfIsLocallyDiscrete` / `oplaxFunctorOfIsLocallyDiscrete` 的定义

English:
definition oplaxFunctorOfIsLocallyDiscrete
  body: obj
  map := map
  map₂ φ := eqToHom (by
    obtain rfl := obj_ext_of_isDiscrete φ
    dsimp)
  mapId := mapId
  mapComp := mapComp
  mapComp_naturality_left η := by
    obtain rfl := obj_ext_of_isDiscrete η
    simp
  mapComp_naturality_right _ _ _ η := by
    obtain rfl := obj_ext_of_isDiscrete η


中文:
定义 oplaxFunctorOfIsLocallyDiscrete
  定义体: obj
  map := map
  map₂ φ := eqToHom (by
    obtain rfl := obj_ext_of_isDiscrete φ
    dsimp)
  mapId := mapId
  mapComp := mapComp
  mapComp_naturality_left η := by
    obtain rfl := obj_ext_of_isDiscrete η
    simp
  mapComp_naturality_right _ _ _ η := by
    obtain rfl := obj_ext_of_isDiscrete η


Depends on / 依赖: cat_disch, eqToHom, fun_, mapComp, mapComp_naturality_left, obj_e, obj_ext_of_isDiscrete
-/
def oplaxFunctorOfIsLocallyDiscrete
    {B C : Type*} [Bicategory B] [IsLocallyDiscrete B] [Bicategory C]
    (obj : B -> C)
    (map : forall {b b' : B}, (b ⟶ b') -> (obj b ⟶ obj b'))
    (mapId : forall (b : B), map (𝟙 b) ⟶ 𝟙 _)
    (mapComp : forall {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂), map (f ≫ g) ⟶ map f ≫ map g)
    (map₂_associator : forall {b₀ b₁ b₂ b₃ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃),
      eqToHom (by simp) ≫ mapComp f (g ≫ h) ≫ map f ◁ mapComp g h =
        mapComp (f ≫ g) h ≫ mapComp f g ▷ map h ≫ (α_ (map f) (map g) (map h)).hom := by
          cat_disch)
    (map₂_left_unitor : forall {b₀ b₁ : B} (f : b₀ ⟶ b₁),
      mapComp (𝟙 b₀) f ≫ mapId b₀ ▷ map f ≫ (fun_ (map f)).hom = eqToHom (by simp) := by
        cat_disch)
    (map₂_right_unitor : forall {b₀ b₁ : B} (f : b₀ ⟶ b₁),
      mapComp f (𝟙 b₁) ≫ map f ◁ mapId b₁ ≫ (ρ_ (map f)).hom = eqToHom (by simp) := by
        cat_disch) :
    B ⥤ᵒᵖᴸ C where
  obj := obj
  map := map
  map₂ φ := eqToHom (by
    obtain rfl := obj_ext_of_isDiscrete φ
    dsimp)
  mapId := mapId
  mapComp := mapComp
  mapComp_naturality_left η := by
    obtain rfl := obj_ext_of_isDiscrete η
    simp
  mapComp_naturality_right _ _ _ η := by
    obtain rfl := obj_ext_of_isDiscrete η
    simp

section

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

/--
A functor between two categories `C` and `D` can be lifted to a pseudofunctor between the
corresponding locally discrete bicategories.
-/
@[simps! obj map mapId mapComp]
/--
Definition of `Functor.toPseudofunctor` / `Functor.toPseudofunctor` 的定义

English:
definition Functor.toPseudofunctor
  signature: : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete D)
  body: pseudofunctorOfIsLocallyDiscrete
    (fun ⟨X⟩ => .mk <| F.obj X) (fun ⟨f⟩ => (F.map f).toLoc)
    (fun ⟨X⟩ => eqToIso (by simp [CategoryStruct.id]))
    (fun ⟨f⟩ ⟨g⟩ => eqToIso (by simp [CategoryStruct.comp]))

@[deprecated (since := "2026-02-08")] alias Functor.toPseudoFunctor := Functor.toPseudofu

中文:
定义 Functor.toPseudofunctor
  签名: : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete D)
  定义体: pseudofunctorOfIsLocallyDiscrete
    (fun ⟨X⟩ => .mk <| F.obj X) (fun ⟨f⟩ => (F.map f).toLoc)
    (fun ⟨X⟩ => eqToIso (by simp [CategoryStruct.id]))
    (fun ⟨f⟩ ⟨g⟩ => eqToIso (by simp [CategoryStruct.comp]))

@[deprecated (since := "2026-02-08")] alias Functor.toPseudoFunctor := Functor.toPseudofu

Depends on / 依赖: CategoryStruct, CategoryStruct.comp, CategoryStruct.id, F.map, F.obj, eqToIso, pseudofunctorOfIsLocallyDiscrete
-/
def Functor.toPseudofunctor : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete D) :=
  pseudofunctorOfIsLocallyDiscrete
    (fun ⟨X⟩ => .mk <| F.obj X) (fun ⟨f⟩ => (F.map f).toLoc)
    (fun ⟨X⟩ => eqToIso (by simp [CategoryStruct.id]))
    (fun ⟨f⟩ ⟨g⟩ => eqToIso (by simp [CategoryStruct.comp]))

@[deprecated (since := "2026-02-08")] alias Functor.toPseudoFunctor := Functor.toPseudofunctor

/--
A functor between two categories `C` and `D` can be lifted to an oplax functor between the
corresponding locally discrete bicategories.

This is just an abbreviation of `Functor.toPseudofunctor.toOplax`.
-/
@[simps! map]
/--
Definition of `Functor.toOplaxFunctor` / `Functor.toOplaxFunctor` 的定义

English:
abbreviation Functor.toOplaxFunctor
  signature: : LocallyDiscrete C ⥤ᵒᵖᴸ (LocallyDiscrete D)
  body: F.toPseudofunctor.toOplax

中文:
缩写 Functor.toOplaxFunctor
  签名: : LocallyDiscrete C ⥤ᵒᵖᴸ (LocallyDiscrete D)
  定义体: F.toPseudofunctor.toOplax

Depends on / 依赖: F.toPseudofunctor.toOplax, toOplax, toPseudofunctor
-/
abbrev Functor.toOplaxFunctor : LocallyDiscrete C ⥤ᵒᵖᴸ (LocallyDiscrete D) :=
  F.toPseudofunctor.toOplax

end

section

variable {I B : Type*} [Category* I] [Bicategory B] [Strict B] (F : I ⥤ B)

attribute [local simp]
  Strict.leftUnitor_eqToIso Strict.rightUnitor_eqToIso Strict.associator_eqToIso

/--
If `B` is a strict bicategory and `I` is a (1-)category, any functor (of 1-categories) `I ⥤ B` can
be promoted to a pseudofunctor from `LocallyDiscrete I` to `B`.
-/
@[simps! obj map mapId mapComp]
/--
Definition of `Functor.toPseudofunctor'` / `Functor.toPseudofunctor'` 的定义

English:
definition Functor.toPseudofunctor'
  signature: : LocallyDiscrete I ⥤ᵖ B
  body: pseudofunctorOfIsLocallyDiscrete
    (fun ⟨X⟩ => F.obj X) (fun ⟨f⟩ => F.map f)
    (fun ⟨X⟩ => eqToIso (by simp [CategoryStruct.id]))
    (fun f g => eqToIso (by obtain ⟨f⟩ := f; obtain ⟨g⟩ := g; simp [CategoryStruct.comp]))

@[deprecated (since := "2026-02-08")] alias Functor.toPseudoFunctor' := Fu

中文:
定义 Functor.toPseudofunctor'
  签名: : LocallyDiscrete I ⥤ᵖ B
  定义体: pseudofunctorOfIsLocallyDiscrete
    (fun ⟨X⟩ => F.obj X) (fun ⟨f⟩ => F.map f)
    (fun ⟨X⟩ => eqToIso (by simp [CategoryStruct.id]))
    (fun f g => eqToIso (by obtain ⟨f⟩ := f; obtain ⟨g⟩ := g; simp [CategoryStruct.comp]))

@[deprecated (since := "2026-02-08")] alias Functor.toPseudoFunctor' := Fu

Depends on / 依赖: CategoryStruct, CategoryStruct.comp, CategoryStruct.id, F.map, F.obj, eqToIso, pseudofunctorOfIsLocallyDiscrete
-/
def Functor.toPseudofunctor' : LocallyDiscrete I ⥤ᵖ B :=
  pseudofunctorOfIsLocallyDiscrete
    (fun ⟨X⟩ => F.obj X) (fun ⟨f⟩ => F.map f)
    (fun ⟨X⟩ => eqToIso (by simp [CategoryStruct.id]))
    (fun f g => eqToIso (by obtain ⟨f⟩ := f; obtain ⟨g⟩ := g; simp [CategoryStruct.comp]))

@[deprecated (since := "2026-02-08")] alias Functor.toPseudoFunctor' := Functor.toPseudofunctor'

/--
If `B` is a strict bicategory and `I` is a (1-)category, any functor (of 1-categories) `I ⥤ B` can
be promoted to an oplax functor from `LocallyDiscrete I` to `B`.
-/
@[simps! map]
/--
Definition of `Functor.toOplaxFunctor'` / `Functor.toOplaxFunctor'` 的定义

English:
abbreviation Functor.toOplaxFunctor'
  signature: : LocallyDiscrete I ⥤ᵒᵖᴸ B
  body: F.toPseudofunctor'.toOplax

中文:
缩写 Functor.toOplaxFunctor'
  签名: : LocallyDiscrete I ⥤ᵒᵖᴸ B
  定义体: F.toPseudofunctor'.toOplax

Depends on / 依赖: F.toPseudofunctor, toOplax, toPseudofunctor
-/
abbrev Functor.toOplaxFunctor' : LocallyDiscrete I ⥤ᵒᵖᴸ B :=
  F.toPseudofunctor'.toOplax

end

namespace LocallyDiscrete

/-- Constructor for pseudofunctors from a locally discrete bicategory. In that
case, we do not need to provide the `map₂` field of pseudofunctors. -/
@[simps! obj map mapId mapComp]
/--
Definition of `mkPseudofunctor` / `mkPseudofunctor` 的定义

English:
definition mkPseudofunctor
  signature: {B₀ C : Type*} [Category* B₀] [Bicategory C]
  body: pseudofunctorOfIsLocallyDiscrete (fun b => obj b.as) (fun f => map f.as)
    (fun _ => mapId _) (fun _ _ => mapComp _ _) (fun _ _ _ => map₂_associator _ _ _)
    (fun _ => map₂_left_unitor _) (fun _ => map₂_right_unitor _)

中文:
定义 mkPseudofunctor
  签名: {B₀ C : 类型} [Category* B₀] [Bicategory C]
  定义体: pseudofunctorOfIsLocallyDiscrete (fun b => obj b.as) (fun f => map f.as)
    (fun _ => mapId _) (fun _ _ => mapComp _ _) (fun _ _ _ => map₂_associator _ _ _)
    (fun _ => map₂_left_unitor _) (fun _ => map₂_right_unitor _)

Depends on / 依赖: LocallyDiscrete, b.as, cat_disch, eqToHom, f.as, fun_, mapComp, pseudofunctorOfIsLocallyDiscrete
-/
def mkPseudofunctor {B₀ C : Type*} [Category* B₀] [Bicategory C]
    (obj : B₀ -> C)
    (map : forall {b b' : B₀}, (b ⟶ b') -> (obj b ⟶ obj b'))
    (mapId : forall (b : B₀), map (𝟙 b) ≅ 𝟙 _)
    (mapComp : forall {b₀ b₁ b₂ : B₀} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂), map (f ≫ g) ≅ map f ≫ map g)
    (map₂_associator : forall {b₀ b₁ b₂ b₃ : B₀} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃),
      (mapComp (f ≫ g) h).hom ≫
        (mapComp f g).hom ▷ map h ≫ (α_ (map f) (map g) (map h)).hom ≫
          map f ◁ (mapComp g h).inv ≫ (mapComp f (g ≫ h)).inv = eqToHom (by simp) := by cat_disch)
    (map₂_left_unitor : forall {b₀ b₁ : B₀} (f : b₀ ⟶ b₁),
      (mapComp (𝟙 b₀) f).hom ≫ (mapId b₀).hom ▷ map f ≫ (fun_ (map f)).hom = eqToHom (by simp) := by
        cat_disch)
    (map₂_right_unitor : forall {b₀ b₁ : B₀} (f : b₀ ⟶ b₁),
      (mapComp f (𝟙 b₁)).hom ≫ map f ◁ (mapId b₁).hom ≫ (ρ_ (map f)).hom = eqToHom (by simp) := by
        cat_disch) :
    LocallyDiscrete B₀ ⥤ᵖ C :=
  pseudofunctorOfIsLocallyDiscrete (fun b => obj b.as) (fun f => map f.as)
    (fun _ => mapId _) (fun _ _ => mapComp _ _) (fun _ _ _ => map₂_associator _ _ _)
    (fun _ => map₂_left_unitor _) (fun _ => map₂_right_unitor _)

end LocallyDiscrete

end CategoryTheory
