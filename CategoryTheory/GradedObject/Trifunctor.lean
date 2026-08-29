/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.GradedObject.Bifunctor
public import Mathlib.CategoryTheory.Functor.Trifunctor
/-!
# The action of trifunctors on graded objects

Given a trifunctor `F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` and types `I₁`, `I₂` and `I₃`, we define a functor
`GradedObject I₁ C₁ ⥤ GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤ GradedObject (I₁ × I₂ × I₃) C₄`
(see `mapTrifunctor`). When we have a map `p : I₁ × I₂ × I₃ → J` and suitable coproducts
exist, we define a functor
`GradedObject I₁ C₁ ⥤ GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤ GradedObject J C₄`
(see `mapTrifunctorMap`) which sends graded objects `X₁`, `X₂`, `X₃` to the graded object
which sets `j` to the coproduct of the objects `((F.obj (X₁ i₁)).obj (X₂ i₂)).obj (X₃ i₃)`
for `p ⟨i₁, i₂, i₃⟩ = j`.

This shall be used in order to construct the associator isomorphism for the monoidal
category structure on `GradedObject I C` induced by a monoidal structure on `C` and
an additive monoid structure on `I` (TODO @joelriou).

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

variable {C₁ C₂ C₃ C₄ C₁₂ C₂₃ : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄] [Category* C₁₂] [Category* C₂₃]

namespace GradedObject

section

variable (F F' : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄)

set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `mapTrifunctor`. -/
@[simps]
/--
Definition of `mapTrifunctorObj` / `mapTrifunctorObj` 的定义

English:
definition mapTrifunctorObj
  signature: {I₁ : Type*} (X₁ : GradedObject I₁ C₁) (I₂ I₃ : Type*)
  body: { obj := fun X₃ x => ((F.obj (X₁ x.1)).obj (X₂ x.2.1)).obj (X₃ x.2.2)
      map := fun {_ _} φ x => ((F.obj (X₁ x.1)).obj (X₂ x.2.1)).map (φ x.2.2) }
  map {X₂ Y₂} φ :=
    { app := fun X₃ x => ((F.obj (X₁ x.1)).map (φ x.2.1)).app (X₃ x.2.2) }

中文:
定义 mapTrifunctorObj
  签名: {I₁ : 类型} (X₁ : GradedObject I₁ C₁) (I₂ I₃ : 类型)
  定义体: { obj := fun X₃ x => ((F.obj (X₁ x.1)).obj (X₂ x.2.1)).obj (X₃ x.2.2)
      map := fun {_ _} φ x => ((F.obj (X₁ x.1)).obj (X₂ x.2.1)).map (φ x.2.2) }
  map {X₂ Y₂} φ :=
    { app := fun X₃ x => ((F.obj (X₁ x.1)).map (φ x.2.1)).app (X₃ x.2.2) }

Depends on / 依赖: F.obj
-/
def mapTrifunctorObj {I₁ : Type*} (X₁ : GradedObject I₁ C₁) (I₂ I₃ : Type*) :
    GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤ GradedObject (I₁ × I₂ × I₃) C₄ where
  obj X₂ :=
    { obj := fun X₃ x => ((F.obj (X₁ x.1)).obj (X₂ x.2.1)).obj (X₃ x.2.2)
      map := fun {_ _} φ x => ((F.obj (X₁ x.1)).obj (X₂ x.2.1)).map (φ x.2.2) }
  map {X₂ Y₂} φ :=
    { app := fun X₃ x => ((F.obj (X₁ x.1)).map (φ x.2.1)).app (X₃ x.2.2) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given a trifunctor `F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` and types `I₁`, `I₂`, `I₃`,
this is the obvious functor
`GradedObject I₁ C₁ ⥤ GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤ GradedObject (I₁ × I₂ × I₃) C₄`.
-/
@[simps]
/--
Definition of `mapTrifunctor` / `mapTrifunctor` 的定义

English:
definition mapTrifunctor
  signature: (I₁ I₂ I₃ : Type*)
  body: mapTrifunctorObj F X₁ I₂ I₃
  map {X₁ Y₁} φ :=
    { app := fun X₂ =>
        { app := fun X₃ x => ((F.map (φ x.1)).app (X₂ x.2.1)).app (X₃ x.2.2) }
      naturality := fun {X₂ Y₂} ψ => by
        ext X₃ x
        dsimp
        simp only [← NatTrans.comp_app]
        congr 1
        rw [NatTrans.nat

中文:
定义 mapTrifunctor
  签名: (I₁ I₂ I₃ : 类型)
  定义体: mapTrifunctorObj F X₁ I₂ I₃
  map {X₁ Y₁} φ :=
    { app := fun X₂ =>
        { app := fun X₃ x => ((F.map (φ x.1)).app (X₂ x.2.1)).app (X₃ x.2.2) }
      naturality := fun {X₂ Y₂} ψ => by
        ext X₃ x
        dsimp
        simp only [← NatTrans.comp_app]
        congr 1
        rw [NatTrans.nat

Depends on / 依赖: mapTrifunctorObj
-/
def mapTrifunctor (I₁ I₂ I₃ : Type*) :
    GradedObject I₁ C₁ ⥤ GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤
      GradedObject (I₁ × I₂ × I₃) C₄ where
  obj X₁ := mapTrifunctorObj F X₁ I₂ I₃
  map {X₁ Y₁} φ :=
    { app := fun X₂ =>
        { app := fun X₃ x => ((F.map (φ x.1)).app (X₂ x.2.1)).app (X₃ x.2.2) }
      naturality := fun {X₂ Y₂} ψ => by
        ext X₃ x
        dsimp
        simp only [← NatTrans.comp_app]
        congr 1
        rw [NatTrans.naturality] }
end

section

variable {F F' : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `mapTrifunctor F I₁ I₂ I₃ ⟶ mapTrifunctor F' I₁ I₂ I₃`
induced by a natural transformation `F ⟶ F'` of trifunctors. -/
@[simps]
/--
Definition of `mapTrifunctorMapNatTrans` / `mapTrifunctorMapNatTrans` 的定义

English:
definition mapTrifunctorMapNatTrans
  signature: (α : F ⟶ F') (I₁ I₂ I₃ : Type*)
  body: { app := fun X₂ =>
        { app := fun _ _ => ((α.app _).app _).app _ }
      naturality := fun {X₂ Y₂} φ => by
        ext X₃ ⟨i₁, i₂, i₃⟩
        dsimp
        simp only [← NatTrans.comp_app, NatTrans.naturality] }
  naturality := fun {X₁ Y₁} φ => by
    ext X₂ X₃ ⟨i₁, i₂, i₃⟩
    dsimp
    simp 

中文:
定义 mapTrifunctorMapNatTrans
  签名: (α : F ⟶ F') (I₁ I₂ I₃ : 类型)
  定义体: { app := fun X₂ =>
        { app := fun _ _ => ((α.app _).app _).app _ }
      naturality := fun {X₂ Y₂} φ => by
        ext X₃ ⟨i₁, i₂, i₃⟩
        dsimp
        simp only [← NatTrans.comp_app, NatTrans.naturality] }
  naturality := fun {X₁ Y₁} φ => by
    ext X₂ X₃ ⟨i₁, i₂, i₃⟩
    dsimp
    simp 

Depends on / 依赖: NatTrans, NatTrans.comp_app, NatTrans.naturality, comp_app, naturality
-/
def mapTrifunctorMapNatTrans (α : F ⟶ F') (I₁ I₂ I₃ : Type*) :
    mapTrifunctor F I₁ I₂ I₃ ⟶ mapTrifunctor F' I₁ I₂ I₃ where
  app X₁ :=
    { app := fun X₂ =>
        { app := fun _ _ => ((α.app _).app _).app _ }
      naturality := fun {X₂ Y₂} φ => by
        ext X₃ ⟨i₁, i₂, i₃⟩
        dsimp
        simp only [← NatTrans.comp_app, NatTrans.naturality] }
  naturality := fun {X₁ Y₁} φ => by
    ext X₂ X₃ ⟨i₁, i₂, i₃⟩
    dsimp
    simp only [← NatTrans.comp_app, NatTrans.naturality]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism `mapTrifunctor F I₁ I₂ I₃ ≅ mapTrifunctor F' I₁ I₂ I₃`
induced by a natural isomorphism `F ≅ F'` of trifunctors. -/
@[simps]
/--
Definition of `mapTrifunctorMapIso` / `mapTrifunctorMapIso` 的定义

English:
definition mapTrifunctorMapIso
  signature: (e : F ≅ F') (I₁ I₂ I₃ : Type*)
  body: mapTrifunctorMapNatTrans e.hom I₁ I₂ I₃
  inv := mapTrifunctorMapNatTrans e.inv I₁ I₂ I₃
  hom_inv_id := by
    ext X₁ X₂ X₃ ⟨i₁, i₂, i₃⟩
    dsimp
    simp only [← NatTrans.comp_app, e.hom_inv_id, NatTrans.id_app]
  inv_hom_id := by
    ext X₁ X₂ X₃ ⟨i₁, i₂, i₃⟩
    dsimp
    simp only [← NatTrans.

中文:
定义 mapTrifunctorMapIso
  签名: (e : F ≅ F') (I₁ I₂ I₃ : 类型)
  定义体: mapTrifunctorMapNatTrans e.hom I₁ I₂ I₃
  inv := mapTrifunctorMapNatTrans e.inv I₁ I₂ I₃
  hom_inv_id := by
    ext X₁ X₂ X₃ ⟨i₁, i₂, i₃⟩
    dsimp
    simp only [← NatTrans.comp_app, e.hom_inv_id, NatTrans.id_app]
  inv_hom_id := by
    ext X₁ X₂ X₃ ⟨i₁, i₂, i₃⟩
    dsimp
    simp only [← NatTrans.

Depends on / 依赖: e.hom, mapTrifunctorMapNatTrans
-/
def mapTrifunctorMapIso (e : F ≅ F') (I₁ I₂ I₃ : Type*) :
    mapTrifunctor F I₁ I₂ I₃ ≅ mapTrifunctor F' I₁ I₂ I₃ where
  hom := mapTrifunctorMapNatTrans e.hom I₁ I₂ I₃
  inv := mapTrifunctorMapNatTrans e.inv I₁ I₂ I₃
  hom_inv_id := by
    ext X₁ X₂ X₃ ⟨i₁, i₂, i₃⟩
    dsimp
    simp only [← NatTrans.comp_app, e.hom_inv_id, NatTrans.id_app]
  inv_hom_id := by
    ext X₁ X₂ X₃ ⟨i₁, i₂, i₃⟩
    dsimp
    simp only [← NatTrans.comp_app, e.inv_hom_id, NatTrans.id_app]

end

section

variable (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄)
variable {I₁ I₂ I₃ J : Type*} (p : I₁ × I₂ × I₃ -> J)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `mapTrifunctorMapObj` / `mapTrifunctorMapObj` 的定义

English:
definition mapTrifunctorMapObj
  signature: (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂)
  body: ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).mapObj p

中文:
定义 mapTrifunctorMapObj
  签名: (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂)
  定义体: ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).mapObj p

Depends on / 依赖: mapObj, mapTrifunctor
-/
noncomputable def mapTrifunctorMapObj (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂)
    (X₃ : GradedObject I₃ C₃)
    [HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p] :
    GradedObject J C₄ :=
  ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).mapObj p

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `ιMapTrifunctorMapObj` / `ιMapTrifunctorMapObj` 的定义

English:
definition ιMapTrifunctorMapObj
  signature: (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂)
  body: ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).ιMapObj p ⟨i₁, i₂, i₃⟩ j h

中文:
定义 ιMapTrifunctorMapObj
  签名: (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂)
  定义体: ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).ιMapObj p ⟨i₁, i₂, i₃⟩ j h

Depends on / 依赖: mapTrifunctor
-/
noncomputable def ιMapTrifunctorMapObj (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂)
    (X₃ : GradedObject I₃ C₃) (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) (h : p ⟨i₁, i₂, i₃⟩ = j)
    [HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p] :
    ((F.obj (X₁ i₁)).obj (X₂ i₂)).obj (X₃ i₃) ⟶ mapTrifunctorMapObj F p X₁ X₂ X₃ j :=
  ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃).ιMapObj p ⟨i₁, i₂, i₃⟩ j h

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `mapTrifunctorMapMap` / `mapTrifunctorMapMap` 的定义

English:
definition mapTrifunctorMapMap
  signature: {X₁ Y₁ : GradedObject I₁ C₁} (f₁ : X₁ ⟶ Y₁)
  body: GradedObject.mapMap ((((mapTrifunctor F I₁ I₂ I₃).map f₁).app X₂).app X₃ ≫
    (((mapTrifunctor F I₁ I₂ I₃).obj Y₁).map f₂).app X₃ ≫
    (((mapTrifunctor F I₁ I₂ I₃).obj Y₁).obj Y₂).map f₃) p

中文:
定义 mapTrifunctorMapMap
  签名: {X₁ Y₁ : GradedObject I₁ C₁} (f₁ : X₁ ⟶ Y₁)
  定义体: GradedObject.mapMap ((((mapTrifunctor F I₁ I₂ I₃).map f₁).app X₂).app X₃ ≫
    (((mapTrifunctor F I₁ I₂ I₃).obj Y₁).map f₂).app X₃ ≫
    (((mapTrifunctor F I₁ I₂ I₃).obj Y₁).obj Y₂).map f₃) p

Depends on / 依赖: GradedObject, GradedObject.mapMap, mapMap, mapTrifunctor
-/
noncomputable def mapTrifunctorMapMap {X₁ Y₁ : GradedObject I₁ C₁} (f₁ : X₁ ⟶ Y₁)
    {X₂ Y₂ : GradedObject I₂ C₂} (f₂ : X₂ ⟶ Y₂)
    {X₃ Y₃ : GradedObject I₃ C₃} (f₃ : X₃ ⟶ Y₃)
    [HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p]
    [HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj Y₁).obj Y₂).obj Y₃) p] :
    mapTrifunctorMapObj F p X₁ X₂ X₃ ⟶ mapTrifunctorMapObj F p Y₁ Y₂ Y₃ :=
  GradedObject.mapMap ((((mapTrifunctor F I₁ I₂ I₃).map f₁).app X₂).app X₃ ≫
    (((mapTrifunctor F I₁ I₂ I₃).obj Y₁).map f₂).app X₃ ≫
    (((mapTrifunctor F I₁ I₂ I₃).obj Y₁).obj Y₂).map f₃) p

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `ι_mapTrifunctorMapMap` / 引理 `ι_mapTrifunctorMapMap`

English:
lemma ι_mapTrifunctorMapMap
  statement: {X₁ Y₁ : GradedObject I₁ C₁} (f₁ : X₁ ⟶ Y₁)
  proof: by
  dsimp only [ιMapTrifunctorMapObj, mapTrifunctorMapMap]
  rw [ι_mapMap]
  dsimp
  rw [assoc]; rw [assoc]

@[ext]

中文:
引理 ι_mapTrifunctorMapMap
  结论: {X₁ Y₁ : GradedObject I₁ C₁} (f₁ : X₁ ⟶ Y₁)
  证明: by
  dsimp only [ιMapTrifunctorMapObj, mapTrifunctorMapMap]
  rw [ι_mapMap]
  dsimp
  rw [assoc]; rw [assoc]

@[ext]

Depends on / 依赖: mapTrifunctorMapMap
-/
lemma ι_mapTrifunctorMapMap {X₁ Y₁ : GradedObject I₁ C₁} (f₁ : X₁ ⟶ Y₁)
    {X₂ Y₂ : GradedObject I₂ C₂} (f₂ : X₂ ⟶ Y₂)
    {X₃ Y₃ : GradedObject I₃ C₃} (f₃ : X₃ ⟶ Y₃)
    [HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p]
    [HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj Y₁).obj Y₂).obj Y₃) p]
    (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J) (h : p ⟨i₁, i₂, i₃⟩ = j) :
    ιMapTrifunctorMapObj F p X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ mapTrifunctorMapMap F p f₁ f₂ f₃ j =
      ((F.map (f₁ i₁)).app (X₂ i₂)).app (X₃ i₃) ≫
        ((F.obj (Y₁ i₁)).map (f₂ i₂)).app (X₃ i₃) ≫
        ((F.obj (Y₁ i₁)).obj (Y₂ i₂)).map (f₃ i₃) ≫
        ιMapTrifunctorMapObj F p Y₁ Y₂ Y₃ i₁ i₂ i₃ j h := by
  dsimp only [ιMapTrifunctorMapObj, mapTrifunctorMapMap]
  rw [ι_mapMap]
  dsimp
  rw [assoc]; rw [assoc]

@[ext]
/--
lemma `mapTrifunctorMapObj_ext` / 引理 `mapTrifunctorMapObj_ext`

English:
lemma mapTrifunctorMapObj_ext
  statement: {X₁ : GradedObject I₁ C₁} {X₂ : GradedObject I₂ C₂}
  proof: by
  apply mapObj_ext
  rintro ⟨i₁, i₂, i₃⟩ hi
  apply h

中文:
引理 mapTrifunctorMapObj_ext
  结论: {X₁ : GradedObject I₁ C₁} {X₂ : GradedObject I₂ C₂}
  证明: by
  apply mapObj_ext
  rintro ⟨i₁, i₂, i₃⟩ hi
  apply h

Depends on / 依赖: mapObj_ext
-/
lemma mapTrifunctorMapObj_ext {X₁ : GradedObject I₁ C₁} {X₂ : GradedObject I₂ C₂}
    {X₃ : GradedObject I₃ C₃} {Y : C₄} (j : J)
    [HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p]
    {φ φ' : mapTrifunctorMapObj F p X₁ X₂ X₃ j ⟶ Y}
    (h : forall (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (h : p ⟨i₁, i₂, i₃⟩ = j),
      ιMapTrifunctorMapObj F p X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ φ =
        ιMapTrifunctorMapObj F p X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ φ') : φ = φ' := by
  apply mapObj_ext
  rintro ⟨i₁, i₂, i₃⟩ hi
  apply h

instance (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂) (X₃ : GradedObject I₃ C₃)
    [h : HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p] :
    HasMap (((mapTrifunctorObj F X₁ I₂ I₃).obj X₂).obj X₃) p := h

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a trifunctor `F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄`, a map `p : I₁ × I₂ × I₃ → J`, and
graded objects `X₁ : GradedObject I₁ C₁`, `X₂ : GradedObject I₂ C₂` and `X₃ : GradedObject I₃ C₃`,
this is the `J`-graded object sending `j` to the coproduct of
`((F.obj (X₁ i₁)).obj (X₂ i₂)).obj (X₃ i₃)` for `p ⟨i₁, i₂, i₃⟩ = j`. -/
@[simps]
/--
Definition of `mapTrifunctorMapFunctorObj` / `mapTrifunctorMapFunctorObj` 的定义

English:
definition mapTrifunctorMapFunctorObj
  signature: (X₁ : GradedObject I₁ C₁)
  body: { obj := fun X₃ => mapTrifunctorMapObj F p X₁ X₂ X₃
      map := fun {_ _} φ => mapTrifunctorMapMap F p (𝟙 X₁) (𝟙 X₂) φ
      map_id := fun X₃ => by
        ext j i₁ i₂ i₃ h
        simp only [ι_mapTrifunctorMapMap, categoryOfGradedObjects_id, Functor.map_id,
          NatTrans.id_app, id_comp, comp

中文:
定义 mapTrifunctorMapFunctorObj
  签名: (X₁ : GradedObject I₁ C₁)
  定义体: { obj := fun X₃ => mapTrifunctorMapObj F p X₁ X₂ X₃
      map := fun {_ _} φ => mapTrifunctorMapMap F p (𝟙 X₁) (𝟙 X₂) φ
      map_id := fun X₃ => by
        ext j i₁ i₂ i₃ h
        simp only [ι_mapTrifunctorMapMap, categoryOfGradedObjects_id, Functor.map_id,
          NatTrans.id_app, id_comp, comp

Depends on / 依赖: Functor, Functor.map_comp, Functor.map_id, NatTrans, NatTrans.id_app, categoryOfGradedObjects_comp, categoryOfGradedObjects_id, comp_id, id_app, id_comp, mapTrifunctorMapMap, mapTrifunctorMapObj, map_comp, map_id
-/
noncomputable def mapTrifunctorMapFunctorObj (X₁ : GradedObject I₁ C₁)
    [forall X₂ X₃, HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p] :
    GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤ GradedObject J C₄ where
  obj X₂ :=
    { obj := fun X₃ => mapTrifunctorMapObj F p X₁ X₂ X₃
      map := fun {_ _} φ => mapTrifunctorMapMap F p (𝟙 X₁) (𝟙 X₂) φ
      map_id := fun X₃ => by
        ext j i₁ i₂ i₃ h
        simp only [ι_mapTrifunctorMapMap, categoryOfGradedObjects_id, Functor.map_id,
          NatTrans.id_app, id_comp, comp_id]
      map_comp := fun {X₃ Y₃ Z₃} φ ψ => by
        ext j i₁ i₂ i₃ h
        simp only [ι_mapTrifunctorMapMap, categoryOfGradedObjects_id, Functor.map_id,
          NatTrans.id_app, categoryOfGradedObjects_comp, Functor.map_comp, assoc, id_comp,
          ι_mapTrifunctorMapMap_assoc] }
  map {X₂ Y₂} φ :=
    { app := fun X₃ => mapTrifunctorMapMap F p (𝟙 X₁) φ (𝟙 X₃)
      naturality := fun {X₃ Y₃} ψ => by
        ext j i₁ i₂ i₃ h
        dsimp
        simp only [ι_mapTrifunctorMapMap_assoc, categoryOfGradedObjects_id, Functor.map_id,
          NatTrans.id_app, ι_mapTrifunctorMapMap, id_comp, NatTrans.naturality_assoc] }
  map_id X₂ := by
    ext X₃ j i₁ i₂ i₃ h
    simp only [ι_mapTrifunctorMapMap, categoryOfGradedObjects_id, Functor.map_id,
      NatTrans.id_app, id_comp, comp_id]
  map_comp {X₂ Y₂ Z₂} φ ψ := by
    ext X₃ j i₁ i₂ i₃
    simp only [ι_mapTrifunctorMapMap, categoryOfGradedObjects_id, Functor.map_id,
      NatTrans.id_app, categoryOfGradedObjects_comp, Functor.map_comp, NatTrans.comp_app,
      id_comp, assoc, ι_mapTrifunctorMapMap_assoc]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `mapTrifunctorMap` / `mapTrifunctorMap` 的定义

English:
definition mapTrifunctorMap
  body: mapTrifunctorMapFunctorObj F p X₁
  map := fun {X₁ Y₁} φ =>
    { app := fun X₂ =>
        { app := fun X₃ => mapTrifunctorMapMap F p φ (𝟙 X₂) (𝟙 X₃)
          naturality := fun {X₃ Y₃} φ => by
            dsimp
            ext j i₁ i₂ i₃ h
            dsimp
            simp only [ι_mapTrifunctorMap

中文:
定义 mapTrifunctorMap
  定义体: mapTrifunctorMapFunctorObj F p X₁
  map := fun {X₁ Y₁} φ =>
    { app := fun X₂ =>
        { app := fun X₃ => mapTrifunctorMapMap F p φ (𝟙 X₂) (𝟙 X₃)
          naturality := fun {X₃ Y₃} φ => by
            dsimp
            ext j i₁ i₂ i₃ h
            dsimp
            simp only [ι_mapTrifunctorMap

Depends on / 依赖: mapTrifunctorMapFunctorObj
-/
noncomputable def mapTrifunctorMap
    [forall X₁ X₂ X₃, HasMap ((((mapTrifunctor F I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) p] :
    GradedObject I₁ C₁ ⥤ GradedObject I₂ C₂ ⥤ GradedObject I₃ C₃ ⥤ GradedObject J C₄ where
  obj X₁ := mapTrifunctorMapFunctorObj F p X₁
  map := fun {X₁ Y₁} φ =>
    { app := fun X₂ =>
        { app := fun X₃ => mapTrifunctorMapMap F p φ (𝟙 X₂) (𝟙 X₃)
          naturality := fun {X₃ Y₃} φ => by
            dsimp
            ext j i₁ i₂ i₃ h
            dsimp
            simp only [ι_mapTrifunctorMapMap_assoc, categoryOfGradedObjects_id, Functor.map_id,
              NatTrans.id_app, ι_mapTrifunctorMapMap, id_comp, NatTrans.naturality_assoc] }
      naturality := fun {X₂ Y₂} ψ => by
        ext X₃ j
        dsimp
        ext i₁ i₂ i₃ h
        simp only [ι_mapTrifunctorMapMap_assoc, categoryOfGradedObjects_id, Functor.map_id,
          NatTrans.id_app, ι_mapTrifunctorMapMap, id_comp,
          NatTrans.naturality_app_assoc] }

attribute [simps] mapTrifunctorMap

end

section

variable (F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂) (G : C₁₂ ⥤ C₃ ⥤ C₄)
  {I₁ I₂ I₃ J : Type*} (r : I₁ × I₂ × I₃ -> J)

/--
Definition of `BifunctorComp₁₂IndexData` / `BifunctorComp₁₂IndexData` 的定义

English:
structure BifunctorComp₁₂IndexData
  parameters: where
  axioms and operations (4):
    - I₁₂ : Type*
    - p : I₁ × I₂ -> I₁₂
    - q : I₁₂ × I₃ -> J
    - hpq((i : I₁ × I₂ × I₃)) : q ⟨p ⟨i.1, i.2.1⟩, i.2.2⟩ = r i

中文:
结构 BifunctorComp₁₂IndexData
  参数: where
  公理与运算 (4 个):
    - I₁₂ : 类型
    - p : I₁ × I₂ -> I₁₂
    - q : I₁₂ × I₃ -> J
    - hpq((i : I₁ × I₂ × I₃)) : q ⟨p ⟨i.1, i.2.1⟩, i.2.2⟩ = r i
-/
structure BifunctorComp₁₂IndexData where
  /-- an auxiliary type -/
  I₁₂ : Type*
  /-- a map `I₁ × I₂ → I₁₂` -/
  p : I₁ × I₂ -> I₁₂
  /-- a map `I₁₂ × I₃ → J` -/
  q : I₁₂ × I₃ -> J
  hpq (i : I₁ × I₂ × I₃) : q ⟨p ⟨i.1, i.2.1⟩, i.2.2⟩ = r i

variable {r} (ρ₁₂ : BifunctorComp₁₂IndexData r)
  (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂) (X₃ : GradedObject I₃ C₃)

/--
Definition of `HasGoodTrifunctor₁₂Obj` / `HasGoodTrifunctor₁₂Obj` 的定义

English:
abbreviation HasGoodTrifunctor₁₂Obj
  body: forall (i₁₂ : ρ₁₂.I₁₂) (i₃ : I₃), PreservesColimit
    (Discrete.functor (mapObjFun (((mapBifunctor F₁₂ I₁ I₂).obj X₁).obj X₂) ρ₁₂.p i₁₂))
      ((Functor.flip G).obj (X₃ i₃))

中文:
缩写 HasGoodTrifunctor₁₂Obj
  定义体: forall (i₁₂ : ρ₁₂.I₁₂) (i₃ : I₃), PreservesColimit
    (Discrete.functor (mapObjFun (((mapBifunctor F₁₂ I₁ I₂).obj X₁).obj X₂) ρ₁₂.p i₁₂))
      ((Functor.flip G).obj (X₃ i₃))

Depends on / 依赖: Discrete, Discrete.functor, Functor, Functor.flip, PreservesColimit, functor, mapBifunctor, mapObjFun
-/
abbrev HasGoodTrifunctor₁₂Obj :=
  forall (i₁₂ : ρ₁₂.I₁₂) (i₃ : I₃), PreservesColimit
    (Discrete.functor (mapObjFun (((mapBifunctor F₁₂ I₁ I₂).obj X₁).obj X₂) ρ₁₂.p i₁₂))
      ((Functor.flip G).obj (X₃ i₃))

variable [HasMap (((mapBifunctor F₁₂ I₁ I₂).obj X₁).obj X₂) ρ₁₂.p]
  [HasMap (((mapBifunctor G ρ₁₂.I₁₂ I₃).obj (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂)).obj X₃) ρ₁₂.q]

/--
Definition of `ιMapBifunctor₁₂BifunctorMapObj` / `ιMapBifunctor₁₂BifunctorMapObj` 的定义

English:
definition ιMapBifunctor₁₂BifunctorMapObj
  signature: (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
  body: (G.map (ιMapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂ i₁ i₂ _ rfl)).app (X₃ i₃) ≫
    ιMapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ (ρ₁₂.p ⟨i₁, i₂⟩) i₃ j
      (by rw [← h, ← ρ₁₂.hpq])

@[reassoc]

中文:
定义 ιMapBifunctor₁₂BifunctorMapObj
  签名: (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
  定义体: (G.map (ιMapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂ i₁ i₂ _ rfl)).app (X₃ i₃) ≫
    ιMapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ (ρ₁₂.p ⟨i₁, i₂⟩) i₃ j
      (by rw [← h, ← ρ₁₂.hpq])

@[reassoc]

Depends on / 依赖: G.map, mapBifunctorMapObj
-/
noncomputable def ιMapBifunctor₁₂BifunctorMapObj (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : r (i₁, i₂, i₃) = j) :
    (G.obj ((F₁₂.obj (X₁ i₁)).obj (X₂ i₂))).obj (X₃ i₃) ⟶
      mapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ j :=
  (G.map (ιMapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂ i₁ i₂ _ rfl)).app (X₃ i₃) ≫
    ιMapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ (ρ₁₂.p ⟨i₁, i₂⟩) i₃ j
      (by rw [← h, ← ρ₁₂.hpq])

@[reassoc]
/--
lemma `ιMapBifunctor₁₂BifunctorMapObj_eq` / 引理 `ιMapBifunctor₁₂BifunctorMapObj_eq`

English:
lemma ιMapBifunctor₁₂BifunctorMapObj_eq
  statement: (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
  proof: by
  subst h₁₂
  rfl

中文:
引理 ιMapBifunctor₁₂BifunctorMapObj_eq
  结论: (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
  证明: by
  subst h₁₂
  rfl
-/
lemma ιMapBifunctor₁₂BifunctorMapObj_eq (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : r (i₁, i₂, i₃) = j) (i₁₂ : ρ₁₂.I₁₂) (h₁₂ : ρ₁₂.p ⟨i₁, i₂⟩ = i₁₂) :
    ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j h =
      (G.map (ιMapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂ i₁ i₂ i₁₂ h₁₂)).app (X₃ i₃) ≫
      ιMapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ i₁₂ i₃ j
        (by rw [← h₁₂, ← h, ← ρ₁₂.hpq]) := by
  subst h₁₂
  rfl

/--
Definition of `cofan₃MapBifunctor₁₂BifunctorMapObj` / `cofan₃MapBifunctor₁₂BifunctorMapObj` 的定义

English:
definition cofan₃MapBifunctor₁₂BifunctorMapObj
  signature: (j : J)
  body: Cofan.mk (mapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ j)
    (fun ⟨⟨i₁, i₂, i₃⟩, (hi : r ⟨i₁, i₂, i₃⟩ = j)⟩ =>
      ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j hi)

中文:
定义 cofan₃MapBifunctor₁₂BifunctorMapObj
  签名: (j : J)
  定义体: Cofan.mk (mapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ j)
    (fun ⟨⟨i₁, i₂, i₃⟩, (hi : r ⟨i₁, i₂, i₃⟩ = j)⟩ =>
      ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j hi)

Depends on / 依赖: Cofan.mk, mapBifunctorMapObj
-/
noncomputable def cofan₃MapBifunctor₁₂BifunctorMapObj (j : J) :
    ((((mapTrifunctor (bifunctorComp₁₂ F₁₂ G) I₁ I₂ I₃).obj X₁).obj X₂).obj
      X₃).CofanMapObjFun r j :=
  Cofan.mk (mapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ j)
    (fun ⟨⟨i₁, i₂, i₃⟩, (hi : r ⟨i₁, i₂, i₃⟩ = j)⟩ =>
      ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j hi)

variable [H : HasGoodTrifunctor₁₂Obj F₁₂ G ρ₁₂ X₁ X₂ X₃]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitCofan₃MapBifunctor₁₂BifunctorMapObj` / `isColimitCofan₃MapBifunctor₁₂BifunctorMapObj` 的定义

English:
definition isColimitCofan₃MapBifunctor₁₂BifunctorMapObj
  signature: (j : J)
  body: by
  let c₁₂ := fun i₁₂ => (((mapBifunctor F₁₂ I₁ I₂).obj X₁).obj X₂).cofanMapObj ρ₁₂.p i₁₂
  have h₁₂ : forall i₁₂, IsColimit (c₁₂ i₁₂) := fun i₁₂ =>
    (((mapBifunctor F₁₂ I₁ I₂).obj X₁).obj X₂).isColimitCofanMapObj ρ₁₂.p i₁₂
  let c := (((mapBifunctor G ρ₁₂.I₁₂ I₃).obj
    (mapBifunctorMapObj F₁

中文:
定义 isColimitCofan₃MapBifunctor₁₂BifunctorMapObj
  签名: (j : J)
  定义体: by
  let c₁₂ := fun i₁₂ => (((mapBifunctor F₁₂ I₁ I₂).obj X₁).obj X₂).cofanMapObj ρ₁₂.p i₁₂
  have h₁₂ : forall i₁₂, IsColimit (c₁₂ i₁₂) := fun i₁₂ =>
    (((mapBifunctor F₁₂ I₁ I₂).obj X₁).obj X₂).isColimitCofanMapObj ρ₁₂.p i₁₂
  let c := (((mapBifunctor G ρ₁₂.I₁₂ I₃).obj
    (mapBifunctorMapObj F₁

Depends on / 依赖: IsColimit, cofanMapObj, isColimitCofanMapObj, mapBifunctor, mapBifunctorMapObj
-/
noncomputable def isColimitCofan₃MapBifunctor₁₂BifunctorMapObj (j : J) :
    IsColimit (cofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j) := by
  let c₁₂ := fun i₁₂ => (((mapBifunctor F₁₂ I₁ I₂).obj X₁).obj X₂).cofanMapObj ρ₁₂.p i₁₂
  have h₁₂ : forall i₁₂, IsColimit (c₁₂ i₁₂) := fun i₁₂ =>
    (((mapBifunctor F₁₂ I₁ I₂).obj X₁).obj X₂).isColimitCofanMapObj ρ₁₂.p i₁₂
  let c := (((mapBifunctor G ρ₁₂.I₁₂ I₃).obj
    (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂)).obj X₃).cofanMapObj ρ₁₂.q j
  have hc : IsColimit c := (((mapBifunctor G ρ₁₂.I₁₂ I₃).obj
    (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂)).obj X₃).isColimitCofanMapObj ρ₁₂.q j
  let c₁₂' := fun (i : ρ₁₂.q ⁻¹' {j}) => (G.flip.obj (X₃ i.1.2)).mapCocone (c₁₂ i.1.1)
  have hc₁₂' : forall i, IsColimit (c₁₂' i) := fun i => isColimitOfPreserves _ (h₁₂ i.1.1)
  let Z := (((mapTrifunctor (bifunctorComp₁₂ F₁₂ G) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃
  let p' : I₁ × I₂ × I₃ -> ρ₁₂.I₁₂ × I₃ := fun ⟨i₁, i₂, i₃⟩ => ⟨ρ₁₂.p ⟨i₁, i₂⟩, i₃⟩
  let e : forall (i₁₂ : ρ₁₂.I₁₂) (i₃ : I₃), p' ⁻¹' {(i₁₂, i₃)} ≃ ρ₁₂.p ⁻¹' {i₁₂} := fun i₁₂ i₃ =>
    { toFun := fun ⟨⟨i₁, i₂, i₃'⟩, hi⟩ => ⟨⟨i₁, i₂⟩, by cat_disch⟩
      invFun := fun ⟨⟨i₁, i₂⟩, hi⟩ => ⟨⟨i₁, i₂, i₃⟩, by cat_disch⟩
      left_inv := fun ⟨⟨i₁, i₂, i₃'⟩, hi⟩ => by
        obtain rfl : i₃ = i₃' := by cat_disch
        rfl }
  let c₁₂'' : forall (i : ρ₁₂.q ⁻¹' {j}), CofanMapObjFun Z p' (i.1.1, i.1.2) :=
    fun ⟨⟨i₁₂, i₃⟩, hi⟩ => by
      refine (Cocone.precompose (Iso.hom ?_)).obj ((Cocone.whiskeringEquivalence
        (Discrete.equivalence (e i₁₂ i₃))).functor.obj (c₁₂' ⟨⟨i₁₂, i₃⟩, hi⟩))
      refine (Discrete.natIso (fun ⟨⟨i₁, i₂, i₃'⟩, hi⟩ =>
        (G.obj ((F₁₂.obj (X₁ i₁)).obj (X₂ i₂))).mapIso (eqToIso ?_)))
      obtain rfl : i₃' = i₃ := congr_arg _root_.Prod.snd hi
      rfl
  have h₁₂'' : forall i, IsColimit (c₁₂'' i) := fun _ =>
    (IsColimit.precomposeHomEquiv _ _).symm (IsColimit.whiskerEquivalenceEquiv _ (hc₁₂' _))
  refine IsColimit.ofIsoColimit (isColimitCofanMapObjComp Z p' ρ₁₂.q r ρ₁₂.hpq j
    (fun ⟨i₁₂, i₃⟩ h => c₁₂'' ⟨⟨i₁₂, i₃⟩, h⟩) (fun ⟨i₁₂, i₃⟩ h => h₁₂'' ⟨⟨i₁₂, i₃⟩, h⟩) c hc)
    (Cocone.ext (Iso.refl _) (fun ⟨⟨i₁, i₂, i₃⟩, h⟩ => ?_))
  dsimp [Cofan.inj, c₁₂'', Z, p']
  rw [comp_id]; rw [Functor.map_id]; rw [id_comp]
  rfl

variable {F₁₂ G ρ₁₂ X₁ X₂ X₃}

include ρ₁₂ in
/--
lemma `HasGoodTrifunctor₁₂Obj.hasMap` / 引理 `HasGoodTrifunctor₁₂Obj.hasMap`

English:
lemma HasGoodTrifunctor₁₂Obj.hasMap
  proof: fun j => ⟨_, isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j⟩

中文:
引理 HasGoodTrifunctor₁₂Obj.hasMap
  证明: fun j => ⟨_, isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j⟩
-/
lemma HasGoodTrifunctor₁₂Obj.hasMap :
    HasMap ((((mapTrifunctor (bifunctorComp₁₂ F₁₂ G) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) r :=
  fun j => ⟨_, isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j⟩

variable (F₁₂ G ρ₁₂ X₁ X₂ X₃)

section
variable [HasMap ((((mapTrifunctor (bifunctorComp₁₂ F₁₂ G) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) r]

/--
Definition of `mapBifunctorComp₁₂MapObjIso` / `mapBifunctorComp₁₂MapObjIso` 的定义

English:
definition mapBifunctorComp₁₂MapObjIso
  signature: :
  body: isoMk _ _ (fun j => (CofanMapObjFun.iso
    (isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j)).symm)

中文:
定义 mapBifunctorComp₁₂MapObjIso
  签名: :
  定义体: isoMk _ _ (fun j => (CofanMapObjFun.iso
    (isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j)).symm)

Depends on / 依赖: CofanMapObjFun, CofanMapObjFun.iso
-/
noncomputable def mapBifunctorComp₁₂MapObjIso :
    mapTrifunctorMapObj (bifunctorComp₁₂ F₁₂ G) r X₁ X₂ X₃ ≅
    mapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ :=
  isoMk _ _ (fun j => (CofanMapObjFun.iso
    (isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j)).symm)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `ι_mapBifunctorComp₁₂MapObjIso_hom` / 引理 `ι_mapBifunctorComp₁₂MapObjIso_hom`

English:
lemma ι_mapBifunctorComp₁₂MapObjIso_hom
  statement: (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
  proof: by
  dsimp [mapBifunctorComp₁₂MapObjIso]
  apply CofanMapObjFun.ιMapObj_iso_inv

@[reassoc (attr := simp)]

中文:
引理 ι_mapBifunctorComp₁₂MapObjIso_hom
  结论: (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
  证明: by
  dsimp [mapBifunctorComp₁₂MapObjIso]
  apply CofanMapObjFun.ιMapObj_iso_inv

@[reassoc (attr := simp)]

Depends on / 依赖: CofanMapObjFun
-/
lemma ι_mapBifunctorComp₁₂MapObjIso_hom (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : r (i₁, i₂, i₃) = j) :
    ιMapTrifunctorMapObj (bifunctorComp₁₂ F₁₂ G) r X₁ X₂ X₃ i₁ i₂ i₃ j h ≫
      (mapBifunctorComp₁₂MapObjIso F₁₂ G ρ₁₂ X₁ X₂ X₃).hom j =
      ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j h := by
  dsimp [mapBifunctorComp₁₂MapObjIso]
  apply CofanMapObjFun.ιMapObj_iso_inv

@[reassoc (attr := simp)]
/--
lemma `ι_mapBifunctorComp₁₂MapObjIso_inv` / 引理 `ι_mapBifunctorComp₁₂MapObjIso_inv`

English:
lemma ι_mapBifunctorComp₁₂MapObjIso_inv
  statement: (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
  proof: CofanMapObjFun.inj_iso_hom
    (isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j) _ h

中文:
引理 ι_mapBifunctorComp₁₂MapObjIso_inv
  结论: (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
  证明: CofanMapObjFun.inj_iso_hom
    (isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j) _ h

Depends on / 依赖: CofanMapObjFun, CofanMapObjFun.inj_iso_hom, HasWideEqualizers, hasEqualizers_of_hasWideEqualizers, inj_iso_hom
-/
lemma ι_mapBifunctorComp₁₂MapObjIso_inv (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : r (i₁, i₂, i₃) = j) :
    ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫
      (mapBifunctorComp₁₂MapObjIso F₁₂ G ρ₁₂ X₁ X₂ X₃).inv j =
      ιMapTrifunctorMapObj (bifunctorComp₁₂ F₁₂ G) r X₁ X₂ X₃ i₁ i₂ i₃ j h :=
  CofanMapObjFun.inj_iso_hom
    (isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j) _ h

end

variable {X₁ X₂ X₃ F₁₂ G ρ₁₂}
variable {j : J} {A : C₄}

@[ext]
/--
lemma `mapBifunctor₁₂BifunctorMapObj_ext` / 引理 `mapBifunctor₁₂BifunctorMapObj_ext`

English:
lemma mapBifunctor₁₂BifunctorMapObj_ext
  statement: {A : C₄}
  proof: by
  apply Cofan.IsColimit.hom_ext (isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j)
  rintro ⟨i, hi⟩
  exact h _ _ _ hi

中文:
引理 mapBifunctor₁₂BifunctorMapObj_ext
  结论: {A : C₄}
  证明: by
  apply Cofan.IsColimit.hom_ext (isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j)
  rintro ⟨i, hi⟩
  exact h _ _ _ hi

Depends on / 依赖: Cofan.IsColimit.hom_ext, HasWideCoequalizers, IsColimit, hasCoequalizers_of_hasWideCoequalizers, hom_ext
-/
lemma mapBifunctor₁₂BifunctorMapObj_ext {A : C₄}
    {f g : mapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ j ⟶ A}
    (h : forall (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (h : r ⟨i₁, i₂, i₃⟩ = j),
      ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ f =
        ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ g) : f = g := by
  apply Cofan.IsColimit.hom_ext (isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j)
  rintro ⟨i, hi⟩
  exact h _ _ _ hi

section

variable (f : forall (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (_ : r ⟨i₁, i₂, i₃⟩ = j),
  (G.obj ((F₁₂.obj (X₁ i₁)).obj (X₂ i₂))).obj (X₃ i₃) ⟶ A)

/--
Definition of `mapBifunctor₁₂BifunctorDesc` / `mapBifunctor₁₂BifunctorDesc` 的定义

English:
definition mapBifunctor₁₂BifunctorDesc
  signature: :
  body: Cofan.IsColimit.desc (isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j)
    (fun i => f i.1.1 i.1.2.1 i.1.2.2 i.2)

@[reassoc (attr := simp)]

中文:
定义 mapBifunctor₁₂BifunctorDesc
  签名: :
  定义体: Cofan.IsColimit.desc (isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j)
    (fun i => f i.1.1 i.1.2.1 i.1.2.2 i.2)

@[reassoc (attr := simp)]

Depends on / 依赖: Cofan.IsColimit.desc, IsColimit
-/
noncomputable def mapBifunctor₁₂BifunctorDesc :
    mapBifunctorMapObj G ρ₁₂.q (mapBifunctorMapObj F₁₂ ρ₁₂.p X₁ X₂) X₃ j ⟶ A :=
  Cofan.IsColimit.desc (isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j)
    (fun i => f i.1.1 i.1.2.1 i.1.2.2 i.2)

@[reassoc (attr := simp)]
/--
lemma `ι_mapBifunctor₁₂BifunctorDesc` / 引理 `ι_mapBifunctor₁₂BifunctorDesc`

English:
lemma ι_mapBifunctor₁₂BifunctorDesc
  proof: Cofan.IsColimit.fac
    (isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j) _ ⟨_, h⟩

中文:
引理 ι_mapBifunctor₁₂BifunctorDesc
  证明: Cofan.IsColimit.fac
    (isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j) _ ⟨_, h⟩

Depends on / 依赖: Cofan.IsColimit.fac, IsColimit
-/
lemma ι_mapBifunctor₁₂BifunctorDesc
    (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (h : r ⟨i₁, i₂, i₃⟩ = j) :
    ιMapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫
      mapBifunctor₁₂BifunctorDesc f = f i₁ i₂ i₃ h :=
  Cofan.IsColimit.fac
    (isColimitCofan₃MapBifunctor₁₂BifunctorMapObj F₁₂ G ρ₁₂ X₁ X₂ X₃ j) _ ⟨_, h⟩

end

end

section

variable (F : C₁ ⥤ C₂₃ ⥤ C₄) (G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃)
  {I₁ I₂ I₃ J : Type*} (r : I₁ × I₂ × I₃ -> J)

/--
Definition of `BifunctorComp₂₃IndexData` / `BifunctorComp₂₃IndexData` 的定义

English:
structure BifunctorComp₂₃IndexData
  parameters: where
  axioms and operations (4):
    - I₂₃ : Type*
    - p : I₂ × I₃ -> I₂₃
    - q : I₁ × I₂₃ -> J
    - hpq((i : I₁ × I₂ × I₃)) : q ⟨i.1, p i.2⟩ = r i

中文:
结构 BifunctorComp₂₃IndexData
  参数: where
  公理与运算 (4 个):
    - I₂₃ : 类型
    - p : I₂ × I₃ -> I₂₃
    - q : I₁ × I₂₃ -> J
    - hpq((i : I₁ × I₂ × I₃)) : q ⟨i.1, p i.2⟩ = r i
-/
structure BifunctorComp₂₃IndexData where
  /-- an auxiliary type -/
  I₂₃ : Type*
  /-- a map `I₂ × I₃ → I₂₃` -/
  p : I₂ × I₃ -> I₂₃
  /-- a map `I₁ × I₂₃ → J` -/
  q : I₁ × I₂₃ -> J
  hpq (i : I₁ × I₂ × I₃) : q ⟨i.1, p i.2⟩ = r i

variable {r} (ρ₂₃ : BifunctorComp₂₃IndexData r)
  (X₁ : GradedObject I₁ C₁) (X₂ : GradedObject I₂ C₂) (X₃ : GradedObject I₃ C₃)

/--
Definition of `HasGoodTrifunctor₂₃Obj` / `HasGoodTrifunctor₂₃Obj` 的定义

English:
abbreviation HasGoodTrifunctor₂₃Obj
  body: forall (i₁ : I₁) (i₂₃ : ρ₂₃.I₂₃), PreservesColimit (Discrete.functor
    (mapObjFun (((mapBifunctor G₂₃ I₂ I₃).obj X₂).obj X₃) ρ₂₃.p i₂₃)) (F.obj (X₁ i₁))

中文:
缩写 HasGoodTrifunctor₂₃Obj
  定义体: forall (i₁ : I₁) (i₂₃ : ρ₂₃.I₂₃), PreservesColimit (Discrete.functor
    (mapObjFun (((mapBifunctor G₂₃ I₂ I₃).obj X₂).obj X₃) ρ₂₃.p i₂₃)) (F.obj (X₁ i₁))

Depends on / 依赖: Discrete, Discrete.functor, F.obj, PreservesColimit, functor, mapBifunctor, mapObjFun
-/
abbrev HasGoodTrifunctor₂₃Obj :=
  forall (i₁ : I₁) (i₂₃ : ρ₂₃.I₂₃), PreservesColimit (Discrete.functor
    (mapObjFun (((mapBifunctor G₂₃ I₂ I₃).obj X₂).obj X₃) ρ₂₃.p i₂₃)) (F.obj (X₁ i₁))

variable [HasMap (((mapBifunctor G₂₃ I₂ I₃).obj X₂).obj X₃) ρ₂₃.p]
  [HasMap (((mapBifunctor F I₁ ρ₂₃.I₂₃).obj X₁).obj (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃)) ρ₂₃.q]

/--
Definition of `ιMapBifunctorBifunctor₂₃MapObj` / `ιMapBifunctorBifunctor₂₃MapObj` 的定义

English:
definition ιMapBifunctorBifunctor₂₃MapObj
  signature: (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
  body: (F.obj (X₁ i₁)).map (ιMapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃ i₂ i₃ _ rfl) ≫
    ιMapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) i₁ (ρ₂₃.p ⟨i₂, i₃⟩) j
      (by rw [← h, ← ρ₂₃.hpq])

@[reassoc]

中文:
定义 ιMapBifunctorBifunctor₂₃MapObj
  签名: (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
  定义体: (F.obj (X₁ i₁)).map (ιMapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃ i₂ i₃ _ rfl) ≫
    ιMapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) i₁ (ρ₂₃.p ⟨i₂, i₃⟩) j
      (by rw [← h, ← ρ₂₃.hpq])

@[reassoc]

Depends on / 依赖: F.obj, mapBifunctorMapObj
-/
noncomputable def ιMapBifunctorBifunctor₂₃MapObj (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : r (i₁, i₂, i₃) = j) :
    (F.obj (X₁ i₁)).obj ((G₂₃.obj (X₂ i₂)).obj (X₃ i₃)) ⟶
      mapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) j :=
  (F.obj (X₁ i₁)).map (ιMapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃ i₂ i₃ _ rfl) ≫
    ιMapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) i₁ (ρ₂₃.p ⟨i₂, i₃⟩) j
      (by rw [← h, ← ρ₂₃.hpq])

@[reassoc]
/--
lemma `ιMapBifunctorBifunctor₂₃MapObj_eq` / 引理 `ιMapBifunctorBifunctor₂₃MapObj_eq`

English:
lemma ιMapBifunctorBifunctor₂₃MapObj_eq
  statement: (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
  proof: by
  subst h₂₃
  rfl

中文:
引理 ιMapBifunctorBifunctor₂₃MapObj_eq
  结论: (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
  证明: by
  subst h₂₃
  rfl
-/
lemma ιMapBifunctorBifunctor₂₃MapObj_eq (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : r (i₁, i₂, i₃) = j) (i₂₃ : ρ₂₃.I₂₃) (h₂₃ : ρ₂₃.p ⟨i₂, i₃⟩ = i₂₃) :
    ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h =
    (F.obj (X₁ i₁)).map (ιMapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃ i₂ i₃ i₂₃ h₂₃) ≫
      ιMapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) i₁ i₂₃ j
        (by rw [← h, ← h₂₃, ← ρ₂₃.hpq]) := by
  subst h₂₃
  rfl

/--
Definition of `cofan₃MapBifunctorBifunctor₂₃MapObj` / `cofan₃MapBifunctorBifunctor₂₃MapObj` 的定义

English:
definition cofan₃MapBifunctorBifunctor₂₃MapObj
  signature: (j : J)
  body: Cofan.mk (mapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) j)
    (fun ⟨⟨i₁, i₂, i₃⟩, (hi : r ⟨i₁, i₂, i₃⟩ = j)⟩ =>
      ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j hi)

中文:
定义 cofan₃MapBifunctorBifunctor₂₃MapObj
  签名: (j : J)
  定义体: Cofan.mk (mapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) j)
    (fun ⟨⟨i₁, i₂, i₃⟩, (hi : r ⟨i₁, i₂, i₃⟩ = j)⟩ =>
      ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j hi)

Depends on / 依赖: Cofan.mk, mapBifunctorMapObj
-/
noncomputable def cofan₃MapBifunctorBifunctor₂₃MapObj (j : J) :
    ((((mapTrifunctor (bifunctorComp₂₃ F G₂₃) I₁ I₂ I₃).obj X₁).obj X₂).obj
      X₃).CofanMapObjFun r j :=
  Cofan.mk (mapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) j)
    (fun ⟨⟨i₁, i₂, i₃⟩, (hi : r ⟨i₁, i₂, i₃⟩ = j)⟩ =>
      ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j hi)

variable [H : HasGoodTrifunctor₂₃Obj F G₂₃ ρ₂₃ X₁ X₂ X₃]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitCofan₃MapBifunctorBifunctor₂₃MapObj` / `isColimitCofan₃MapBifunctorBifunctor₂₃MapObj` 的定义

English:
definition isColimitCofan₃MapBifunctorBifunctor₂₃MapObj
  signature: (j : J)
  body: by
  let c₂₃ := fun i₂₃ => (((mapBifunctor G₂₃ I₂ I₃).obj X₂).obj X₃).cofanMapObj ρ₂₃.p i₂₃
  have h₂₃ : forall i₂₃, IsColimit (c₂₃ i₂₃) := fun i₂₃ =>
    (((mapBifunctor G₂₃ I₂ I₃).obj X₂).obj X₃).isColimitCofanMapObj ρ₂₃.p i₂₃
  let c := (((mapBifunctor F I₁ ρ₂₃.I₂₃).obj X₁).obj
    (mapBifunctorM

中文:
定义 isColimitCofan₃MapBifunctorBifunctor₂₃MapObj
  签名: (j : J)
  定义体: by
  let c₂₃ := fun i₂₃ => (((mapBifunctor G₂₃ I₂ I₃).obj X₂).obj X₃).cofanMapObj ρ₂₃.p i₂₃
  have h₂₃ : forall i₂₃, IsColimit (c₂₃ i₂₃) := fun i₂₃ =>
    (((mapBifunctor G₂₃ I₂ I₃).obj X₂).obj X₃).isColimitCofanMapObj ρ₂₃.p i₂₃
  let c := (((mapBifunctor F I₁ ρ₂₃.I₂₃).obj X₁).obj
    (mapBifunctorM

Depends on / 依赖: IsColimit, cofanMapObj, isColimitCofanMapObj, mapBifunctor, mapBifunctorMapObj
-/
noncomputable def isColimitCofan₃MapBifunctorBifunctor₂₃MapObj (j : J) :
    IsColimit (cofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j) := by
  let c₂₃ := fun i₂₃ => (((mapBifunctor G₂₃ I₂ I₃).obj X₂).obj X₃).cofanMapObj ρ₂₃.p i₂₃
  have h₂₃ : forall i₂₃, IsColimit (c₂₃ i₂₃) := fun i₂₃ =>
    (((mapBifunctor G₂₃ I₂ I₃).obj X₂).obj X₃).isColimitCofanMapObj ρ₂₃.p i₂₃
  let c := (((mapBifunctor F I₁ ρ₂₃.I₂₃).obj X₁).obj
    (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃)).cofanMapObj ρ₂₃.q j
  have hc : IsColimit c := (((mapBifunctor F I₁ ρ₂₃.I₂₃).obj X₁).obj
    (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃)).isColimitCofanMapObj ρ₂₃.q j
  let c₂₃' := fun (i : ρ₂₃.q ⁻¹' {j}) => (F.obj (X₁ i.1.1)).mapCocone (c₂₃ i.1.2)
  have hc₂₃' : forall i, IsColimit (c₂₃' i) := fun i => isColimitOfPreserves _ (h₂₃ i.1.2)
  let Z := (((mapTrifunctor (bifunctorComp₂₃ F G₂₃) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃
  let p' : I₁ × I₂ × I₃ -> I₁ × ρ₂₃.I₂₃ := fun ⟨i₁, i₂, i₃⟩ => ⟨i₁, ρ₂₃.p ⟨i₂, i₃⟩⟩
  let e : forall (i₁ : I₁) (i₂₃ : ρ₂₃.I₂₃), p' ⁻¹' {(i₁, i₂₃)} ≃ ρ₂₃.p ⁻¹' {i₂₃} := fun i₁ i₂₃ =>
    { toFun := fun ⟨⟨i₁', i₂, i₃⟩, hi⟩ => ⟨⟨i₂, i₃⟩, by cat_disch⟩
      invFun := fun ⟨⟨i₂, i₃⟩, hi⟩ => ⟨⟨i₁, i₂, i₃⟩, by cat_disch⟩
      left_inv := fun ⟨⟨i₁', i₂, i₃⟩, hi⟩ => by
        obtain rfl : i₁ = i₁' := by cat_disch
        rfl }
  let c₂₃'' : forall (i : ρ₂₃.q ⁻¹' {j}), CofanMapObjFun Z p' (i.1.1, i.1.2) :=
    fun ⟨⟨i₁, i₂₃⟩, hi⟩ => by
      refine (Cocone.precompose (Iso.hom ?_)).obj ((Cocone.whiskeringEquivalence
        (Discrete.equivalence (e i₁ i₂₃))).functor.obj (c₂₃' ⟨⟨i₁, i₂₃⟩, hi⟩))
      refine Discrete.natIso (fun ⟨⟨i₁', i₂, i₃⟩, hi⟩ => eqToIso ?_)
      obtain rfl : i₁' = i₁ := congr_arg _root_.Prod.fst hi
      rfl
  have h₂₃'' : forall i, IsColimit (c₂₃'' i) := fun _ =>
    (IsColimit.precomposeHomEquiv _ _).symm (IsColimit.whiskerEquivalenceEquiv _ (hc₂₃' _))
  refine IsColimit.ofIsoColimit (isColimitCofanMapObjComp Z p' ρ₂₃.q r ρ₂₃.hpq j
    (fun ⟨i₁, i₂₃⟩ h => c₂₃'' ⟨⟨i₁, i₂₃⟩, h⟩) (fun ⟨i₁, i₂₃⟩ h => h₂₃'' ⟨⟨i₁, i₂₃⟩, h⟩) c hc)
    (Cocone.ext (Iso.refl _) (fun ⟨⟨i₁, i₂, i₃⟩, h⟩ => ?_))
  dsimp [Cofan.inj, c₂₃'', Z, p', e]
  rw [comp_id]; rw [id_comp]
  rfl

variable {F₁₂ G ρ₁₂ X₁ X₂ X₃}

include ρ₂₃ in
/--
lemma `HasGoodTrifunctor₂₃Obj.hasMap` / 引理 `HasGoodTrifunctor₂₃Obj.hasMap`

English:
lemma HasGoodTrifunctor₂₃Obj.hasMap
  proof: fun j => ⟨_, isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j⟩

中文:
引理 HasGoodTrifunctor₂₃Obj.hasMap
  证明: fun j => ⟨_, isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j⟩
-/
lemma HasGoodTrifunctor₂₃Obj.hasMap :
    HasMap ((((mapTrifunctor (bifunctorComp₂₃ F G₂₃) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) r :=
  fun j => ⟨_, isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j⟩

variable (F₁₂ G ρ₁₂ X₁ X₂ X₃)

section
variable [HasMap ((((mapTrifunctor (bifunctorComp₂₃ F G₂₃) I₁ I₂ I₃).obj X₁).obj X₂).obj X₃) r]

/--
Definition of `mapBifunctorComp₂₃MapObjIso` / `mapBifunctorComp₂₃MapObjIso` 的定义

English:
definition mapBifunctorComp₂₃MapObjIso
  signature: :
  body: isoMk _ _ (fun j => (CofanMapObjFun.iso
    (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j)).symm)

中文:
定义 mapBifunctorComp₂₃MapObjIso
  签名: :
  定义体: isoMk _ _ (fun j => (CofanMapObjFun.iso
    (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j)).symm)

Depends on / 依赖: CofanMapObjFun, CofanMapObjFun.iso
-/
noncomputable def mapBifunctorComp₂₃MapObjIso :
    mapTrifunctorMapObj (bifunctorComp₂₃ F G₂₃) r X₁ X₂ X₃ ≅
    mapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) :=
  isoMk _ _ (fun j => (CofanMapObjFun.iso
    (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j)).symm)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `ι_mapBifunctorComp₂₃MapObjIso_hom` / 引理 `ι_mapBifunctorComp₂₃MapObjIso_hom`

English:
lemma ι_mapBifunctorComp₂₃MapObjIso_hom
  statement: (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
  proof: by
  dsimp [mapBifunctorComp₂₃MapObjIso]
  apply CofanMapObjFun.ιMapObj_iso_inv

@[reassoc (attr := simp)]

中文:
引理 ι_mapBifunctorComp₂₃MapObjIso_hom
  结论: (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
  证明: by
  dsimp [mapBifunctorComp₂₃MapObjIso]
  apply CofanMapObjFun.ιMapObj_iso_inv

@[reassoc (attr := simp)]

Depends on / 依赖: CofanMapObjFun
-/
lemma ι_mapBifunctorComp₂₃MapObjIso_hom (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : r (i₁, i₂, i₃) = j) :
    ιMapTrifunctorMapObj (bifunctorComp₂₃ F G₂₃) r X₁ X₂ X₃ i₁ i₂ i₃ j h ≫
      (mapBifunctorComp₂₃MapObjIso F G₂₃ ρ₂₃ X₁ X₂ X₃).hom j =
      ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h := by
  dsimp [mapBifunctorComp₂₃MapObjIso]
  apply CofanMapObjFun.ιMapObj_iso_inv

@[reassoc (attr := simp)]
/--
lemma `ι_mapBifunctorComp₂₃MapObjIso_inv` / 引理 `ι_mapBifunctorComp₂₃MapObjIso_inv`

English:
lemma ι_mapBifunctorComp₂₃MapObjIso_inv
  statement: (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
  proof: CofanMapObjFun.inj_iso_hom
    (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j) _ h

中文:
引理 ι_mapBifunctorComp₂₃MapObjIso_inv
  结论: (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
  证明: CofanMapObjFun.inj_iso_hom
    (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j) _ h

Depends on / 依赖: CofanMapObjFun, CofanMapObjFun.inj_iso_hom, inj_iso_hom
-/
lemma ι_mapBifunctorComp₂₃MapObjIso_inv (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)
    (h : r (i₁, i₂, i₃) = j) :
    ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫
      (mapBifunctorComp₂₃MapObjIso F G₂₃ ρ₂₃ X₁ X₂ X₃).inv j =
      ιMapTrifunctorMapObj (bifunctorComp₂₃ F G₂₃) r X₁ X₂ X₃ i₁ i₂ i₃ j h :=
  CofanMapObjFun.inj_iso_hom
    (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j) _ h

end

variable {X₁ X₂ X₃ F G₂₃ ρ₂₃}
variable {j : J} {A : C₄}

@[ext]
/--
lemma `mapBifunctorBifunctor₂₃MapObj_ext` / 引理 `mapBifunctorBifunctor₂₃MapObj_ext`

English:
lemma mapBifunctorBifunctor₂₃MapObj_ext
  proof: by
  apply Cofan.IsColimit.hom_ext (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j)
  rintro ⟨i, hi⟩
  exact h _ _ _ hi

中文:
引理 mapBifunctorBifunctor₂₃MapObj_ext
  证明: by
  apply Cofan.IsColimit.hom_ext (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j)
  rintro ⟨i, hi⟩
  exact h _ _ _ hi

Depends on / 依赖: Cofan.IsColimit.hom_ext, IsColimit, hom_ext
-/
lemma mapBifunctorBifunctor₂₃MapObj_ext
    {f g : mapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) j ⟶ A}
    (h : forall (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (h : r ⟨i₁, i₂, i₃⟩ = j),
      ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ f =
        ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ g) : f = g := by
  apply Cofan.IsColimit.hom_ext (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j)
  rintro ⟨i, hi⟩
  exact h _ _ _ hi

section

variable
  (f : forall (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (_ : r ⟨i₁, i₂, i₃⟩ = j),
    (F.obj (X₁ i₁)).obj ((G₂₃.obj (X₂ i₂)).obj (X₃ i₃)) ⟶ A)

/--
Definition of `mapBifunctorBifunctor₂₃Desc` / `mapBifunctorBifunctor₂₃Desc` 的定义

English:
definition mapBifunctorBifunctor₂₃Desc
  signature: :
  body: Cofan.IsColimit.desc (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j)
    (fun i => f i.1.1 i.1.2.1 i.1.2.2 i.2)

@[reassoc (attr := simp)]

中文:
定义 mapBifunctorBifunctor₂₃Desc
  签名: :
  定义体: Cofan.IsColimit.desc (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j)
    (fun i => f i.1.1 i.1.2.1 i.1.2.2 i.2)

@[reassoc (attr := simp)]

Depends on / 依赖: Cofan.IsColimit.desc, IsColimit
-/
noncomputable def mapBifunctorBifunctor₂₃Desc :
    mapBifunctorMapObj F ρ₂₃.q X₁ (mapBifunctorMapObj G₂₃ ρ₂₃.p X₂ X₃) j ⟶ A :=
  Cofan.IsColimit.desc (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j)
    (fun i => f i.1.1 i.1.2.1 i.1.2.2 i.2)

@[reassoc (attr := simp)]
/--
lemma `ι_mapBifunctorBifunctor₂₃Desc` / 引理 `ι_mapBifunctorBifunctor₂₃Desc`

English:
lemma ι_mapBifunctorBifunctor₂₃Desc
  proof: Cofan.IsColimit.fac
    (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j) _ ⟨_, h⟩

中文:
引理 ι_mapBifunctorBifunctor₂₃Desc
  证明: Cofan.IsColimit.fac
    (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j) _ ⟨_, h⟩

Depends on / 依赖: Cofan.IsColimit.fac, IsColimit
-/
lemma ι_mapBifunctorBifunctor₂₃Desc
    (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (h : r ⟨i₁, i₂, i₃⟩ = j) :
    ιMapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫
      mapBifunctorBifunctor₂₃Desc f = f i₁ i₂ i₃ h :=
  Cofan.IsColimit.fac
    (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj F G₂₃ ρ₂₃ X₁ X₂ X₃ j) _ ⟨_, h⟩

end


end

end GradedObject

end CategoryTheory
