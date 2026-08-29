/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.GradedObject
/-!
# The action of bifunctors on graded objects

Given a bifunctor `F : C₁ ⥤ C₂ ⥤ C₃` and types `I` and `J`, we construct an obvious functor
`mapBifunctor F I J : GradedObject I C₁ ⥤ GradedObject J C₂ ⥤ GradedObject (I × J) C₃`.
When we have a map `p : I × J → K` and that suitable coproducts exist, we also get
a functor
`mapBifunctorMap F p : GradedObject I C₁ ⥤ GradedObject J C₂ ⥤ GradedObject K C₃`.

In case `p : I × I → I` is the addition on a monoid and `F` is the tensor product on a monoidal
category `C`, these definitions shall be used in order to construct a monoidal structure
on `GradedObject I C` (TODO @joelriou).

-/

@[expose] public section

namespace CategoryTheory

open Category

variable {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  (F : C₁ ⥤ C₂ ⥤ C₃)

namespace GradedObject

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a bifunctor `F : C₁ ⥤ C₂ ⥤ C₃` and types `I` and `J`, this is the obvious
functor `GradedObject I C₁ ⥤ GradedObject J C₂ ⥤ GradedObject (I × J) C₃`. -/
@[simps]
/--
Definition of `mapBifunctor` / `mapBifunctor` 的定义

English:
definition mapBifunctor
  signature: (I J : Type*)
  body: set_option backward.isDefEq.respectTransparency.types false in
    { obj := fun Y ij => (F.obj (X ij.1)).obj (Y ij.2)
      map := fun φ ij => (F.obj (X ij.1)).map (φ ij.2) }
  map φ :=
    set_option backward.isDefEq.respectTransparency.types false in
    { app := fun Y ij => (F.map (φ ij.1)).app (Y ij.2) }

中文:
定义 mapBifunctor
  签名: (I J : 类型)
  定义体: set_option backward.isDefEq.respectTransparency.types false in
    { obj := fun Y ij => (F.obj (X ij.1)).obj (Y ij.2)
      map := fun φ ij => (F.obj (X ij.1)).map (φ ij.2) }
  map φ :=
    set_option backward.isDefEq.respectTransparency.types false in
    { app := fun Y ij => (F.map (φ ij.1)).app (Y ij.2) }

Depends on / 依赖: F.map, F.obj, HasColimit, HasColimit.mk, backward, backward.isDefEq.respectTransparency.types, cocone, initial, initial.to, isColimit, isDefEq, respectTransparency, set_option
-/
def mapBifunctor (I J : Type*) :
    GradedObject I C₁ ⥤ GradedObject J C₂ ⥤ GradedObject (I × J) C₃ where
  obj X :=
    set_option backward.isDefEq.respectTransparency.types false in
    { obj := fun Y ij => (F.obj (X ij.1)).obj (Y ij.2)
      map := fun φ ij => (F.obj (X ij.1)).map (φ ij.2) }
  map φ :=
    set_option backward.isDefEq.respectTransparency.types false in
    { app := fun Y ij => (F.map (φ ij.1)).app (Y ij.2) }

section

variable {I J K : Type*} (p : I × J -> K)

/--
Definition of `mapBifunctorMapObj` / `mapBifunctorMapObj` 的定义

English:
definition mapBifunctorMapObj
  signature: (X : GradedObject I C₁) (Y : GradedObject J C₂)
  body: (((mapBifunctor F I J).obj X).obj Y).mapObj p

中文:
定义 mapBifunctorMapObj
  签名: (X : GradedObject I C₁) (Y : GradedObject J C₂)
  定义体: (((mapBifunctor F I J).obj X).obj Y).mapObj p

Depends on / 依赖: mapBifunctor, mapObj
-/
noncomputable def mapBifunctorMapObj (X : GradedObject I C₁) (Y : GradedObject J C₂)
    [HasMap (((mapBifunctor F I J).obj X).obj Y) p] : GradedObject K C₃ :=
  (((mapBifunctor F I J).obj X).obj Y).mapObj p

/--
Definition of `ιMapBifunctorMapObj` / `ιMapBifunctorMapObj` 的定义

English:
definition ιMapBifunctorMapObj
  body: (((mapBifunctor F I J).obj X).obj Y).ιMapObj p ⟨i, j⟩ k h

中文:
定义 ιMapBifunctorMapObj
  定义体: (((mapBifunctor F I J).obj X).obj Y).ιMapObj p ⟨i, j⟩ k h

Depends on / 依赖: mapBifunctor
-/
noncomputable def ιMapBifunctorMapObj
    (X : GradedObject I C₁) (Y : GradedObject J C₂)
    [HasMap (((mapBifunctor F I J).obj X).obj Y) p]
    (i : I) (j : J) (k : K) (h : p ⟨i, j⟩ = k) :
    (F.obj (X i)).obj (Y j) ⟶ mapBifunctorMapObj F p X Y k :=
  (((mapBifunctor F I J).obj X).obj Y).ιMapObj p ⟨i, j⟩ k h

/--
Definition of `mapBifunctorMapMap` / `mapBifunctorMapMap` 的定义

English:
definition mapBifunctorMapMap
  signature: {X₁ X₂ : GradedObject I C₁} (f : X₁ ⟶ X₂)
  body: GradedObject.mapMap (((mapBifunctor F I J).map f).app Y₁ ≫
    ((mapBifunctor F I J).obj X₂).map g) p

中文:
定义 mapBifunctorMapMap
  签名: {X₁ X₂ : GradedObject I C₁} (f : X₁ ⟶ X₂)
  定义体: GradedObject.mapMap (((mapBifunctor F I J).map f).app Y₁ ≫
    ((mapBifunctor F I J).obj X₂).map g) p

Depends on / 依赖: GradedObject, GradedObject.mapMap, HasInitial, InitialMonoClass, initial, initial.mono_from, mapBifunctor, mapMap, mono_from
-/
noncomputable def mapBifunctorMapMap {X₁ X₂ : GradedObject I C₁} (f : X₁ ⟶ X₂)
    {Y₁ Y₂ : GradedObject J C₂} (g : Y₁ ⟶ Y₂)
    [HasMap (((mapBifunctor F I J).obj X₁).obj Y₁) p]
    [HasMap (((mapBifunctor F I J).obj X₂).obj Y₂) p] :
    mapBifunctorMapObj F p X₁ Y₁ ⟶ mapBifunctorMapObj F p X₂ Y₂ :=
  GradedObject.mapMap (((mapBifunctor F I J).map f).app Y₁ ≫
    ((mapBifunctor F I J).obj X₂).map g) p

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `ι_mapBifunctorMapMap` / 引理 `ι_mapBifunctorMapMap`

English:
lemma ι_mapBifunctorMapMap
  statement: {X₁ X₂ : GradedObject I C₁} (f : X₁ ⟶ X₂)
  proof: by
  simp [ιMapBifunctorMapObj, mapBifunctorMapMap]

@[ext]

中文:
引理 ι_mapBifunctorMapMap
  结论: {X₁ X₂ : GradedObject I C₁} (f : X₁ ⟶ X₂)
  证明: by
  simp [ιMapBifunctorMapObj, mapBifunctorMapMap]

@[ext]

Depends on / 依赖: mapBifunctorMapMap
-/
lemma ι_mapBifunctorMapMap {X₁ X₂ : GradedObject I C₁} (f : X₁ ⟶ X₂)
    {Y₁ Y₂ : GradedObject J C₂} (g : Y₁ ⟶ Y₂)
    [HasMap (((mapBifunctor F I J).obj X₁).obj Y₁) p]
    [HasMap (((mapBifunctor F I J).obj X₂).obj Y₂) p]
    (i : I) (j : J) (k : K) (h : p ⟨i, j⟩ = k) :
    ιMapBifunctorMapObj F p X₁ Y₁ i j k h ≫ mapBifunctorMapMap F p f g k =
      (F.map (f i)).app (Y₁ j) ≫ (F.obj (X₂ i)).map (g j) ≫
        ιMapBifunctorMapObj F p X₂ Y₂ i j k h := by
  simp [ιMapBifunctorMapObj, mapBifunctorMapMap]

@[ext]
/--
lemma `mapBifunctorMapObj_ext` / 引理 `mapBifunctorMapObj_ext`

English:
lemma mapBifunctorMapObj_ext
  statement: {X : GradedObject I C₁} {Y : GradedObject J C₂} {A : C₃} {k : K}
  proof: by
  apply mapObj_ext
  rintro ⟨i, j⟩ hij
  exact h i j hij

中文:
引理 mapBifunctorMapObj_ext
  结论: {X : GradedObject I C₁} {Y : GradedObject J C₂} {A : C₃} {k : K}
  证明: by
  apply mapObj_ext
  rintro ⟨i, j⟩ hij
  exact h i j hij

Depends on / 依赖: mapObj_ext
-/
lemma mapBifunctorMapObj_ext {X : GradedObject I C₁} {Y : GradedObject J C₂} {A : C₃} {k : K}
    [HasMap (((mapBifunctor F I J).obj X).obj Y) p]
    {f g : mapBifunctorMapObj F p X Y k ⟶ A}
    (h : forall (i : I) (j : J) (hij : p ⟨i, j⟩ = k),
      ιMapBifunctorMapObj F p X Y i j k hij ≫ f = ιMapBifunctorMapObj F p X Y i j k hij ≫ g) :
    f = g := by
  apply mapObj_ext
  rintro ⟨i, j⟩ hij
  exact h i j hij

variable {F p} in
/--
Definition of `mapBifunctorMapObjDesc` / `mapBifunctorMapObjDesc` 的定义

English:
definition mapBifunctorMapObjDesc
  body: descMapObj _ _ (fun ⟨i, j⟩ hij => f i j hij)

@[reassoc (attr := simp)]

中文:
定义 mapBifunctorMapObjDesc
  定义体: descMapObj _ _ (fun ⟨i, j⟩ hij => f i j hij)

@[reassoc (attr := simp)]

Depends on / 依赖: descMapObj
-/
noncomputable def mapBifunctorMapObjDesc
    {X : GradedObject I C₁} {Y : GradedObject J C₂} {A : C₃} {k : K}
    [HasMap (((mapBifunctor F I J).obj X).obj Y) p]
    (f : forall (i : I) (j : J) (_ : p ⟨i, j⟩ = k), (F.obj (X i)).obj (Y j) ⟶ A) :
    mapBifunctorMapObj F p X Y k ⟶ A :=
  descMapObj _ _ (fun ⟨i, j⟩ hij => f i j hij)

@[reassoc (attr := simp)]
/--
lemma `ι_mapBifunctorMapObjDesc` / 引理 `ι_mapBifunctorMapObjDesc`

English:
lemma ι_mapBifunctorMapObjDesc
  statement: {X : GradedObject I C₁} {Y : GradedObject J C₂} {A : C₃} {k : K}
  proof: by
  apply ι_descMapObj

中文:
引理 ι_mapBifunctorMapObjDesc
  结论: {X : GradedObject I C₁} {Y : GradedObject J C₂} {A : C₃} {k : K}
  证明: by
  apply ι_descMapObj
-/
lemma ι_mapBifunctorMapObjDesc {X : GradedObject I C₁} {Y : GradedObject J C₂} {A : C₃} {k : K}
    [HasMap (((mapBifunctor F I J).obj X).obj Y) p]
    (f : forall (i : I) (j : J) (_ : p ⟨i, j⟩ = k), (F.obj (X i)).obj (Y j) ⟶ A)
    (i : I) (j : J) (hij : p ⟨i, j⟩ = k) :
    ιMapBifunctorMapObj F p X Y i j k hij ≫ mapBifunctorMapObjDesc f = f i j hij := by
  apply ι_descMapObj

section

variable {X₁ X₂ : GradedObject I C₁} {Y₁ Y₂ : GradedObject J C₂}
    [HasMap (((mapBifunctor F I J).obj X₁).obj Y₁) p]
    [HasMap (((mapBifunctor F I J).obj X₂).obj Y₂) p]

set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism `mapBifunctorMapObj F p X₁ Y₁ ≅ mapBifunctorMapObj F p X₂ Y₂`
induced by isomorphisms `X₁ ≅ X₂` and `Y₁ ≅ Y₂`. -/
@[simps]
/--
Definition of `mapBifunctorMapMapIso` / `mapBifunctorMapMapIso` 的定义

English:
definition mapBifunctorMapMapIso
  signature: (e : X₁ ≅ X₂) (e' : Y₁ ≅ Y₂)
  body: mapBifunctorMapMap F p e.hom e'.hom
  inv := mapBifunctorMapMap F p e.inv e'.inv
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

中文:
定义 mapBifunctorMapMapIso
  签名: (e : X₁ ≅ X₂) (e' : Y₁ ≅ Y₂)
  定义体: mapBifunctorMapMap F p e.hom e'.hom
  inv := mapBifunctorMapMap F p e.inv e'.inv
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

Depends on / 依赖: e.hom, mapBifunctorMapMap
-/
noncomputable def mapBifunctorMapMapIso (e : X₁ ≅ X₂) (e' : Y₁ ≅ Y₂) :
    mapBifunctorMapObj F p X₁ Y₁ ≅ mapBifunctorMapObj F p X₂ Y₂ where
  hom := mapBifunctorMapMap F p e.hom e'.hom
  inv := mapBifunctorMapMap F p e.inv e'.inv
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

instance (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) [IsIso f] [IsIso g] :
    IsIso (mapBifunctorMapMap F p f g) :=
inferInstanceAs IsIso (mapBifunctorMapMapIso F p (asIso f) (asIso g)).hom

end

attribute [local simp] mapBifunctorMapMap

set_option backward.isDefEq.respectTransparency false in
/-- Given a bifunctor `F : C₁ ⥤ C₂ ⥤ C₃` and a map `p : I × J → K`, this is the
functor `GradedObject I C₁ ⥤ GradedObject J C₂ ⥤ GradedObject K C₃` sending
`X : GradedObject I C₁` and `Y : GradedObject J C₂` to the `K`-graded object sending
`k` to the coproduct of `(F.obj (X i)).obj (Y j)` for `p ⟨i, j⟩ = k`. -/
@[simps]
/--
Definition of `mapBifunctorMap` / `mapBifunctorMap` 的定义

English:
definition mapBifunctorMap
  signature: [forall X Y, HasMap (((mapBifunctor F I J).obj X).obj Y) p]
  body: { obj := fun Y => mapBifunctorMapObj F p X Y
      map := fun ψ => mapBifunctorMapMap F p (𝟙 X) ψ }
  map {X₁ X₂} φ :=
    { app := fun Y => mapBifunctorMapMap F p φ (𝟙 Y)
      naturality := fun {Y₁ Y₂} ψ => by
        dsimp
        simp only [Functor.map_id, NatTrans.id_app, id_comp, comp_id,
          ← mapMap_comp, NatTrans.naturality] }

中文:
定义 mapBifunctorMap
  签名: [对任意 X Y, HasMap (((mapBifunctor F I J).obj X).obj Y) p]
  定义体: { obj := fun Y => mapBifunctorMapObj F p X Y
      map := fun ψ => mapBifunctorMapMap F p (𝟙 X) ψ }
  map {X₁ X₂} φ :=
    { app := fun Y => mapBifunctorMapMap F p φ (𝟙 Y)
      naturality := fun {Y₁ Y₂} ψ => by
        dsimp
        simp only [Functor.map_id, NatTrans.id_app, id_comp, comp_id,
          ← mapMap_comp, NatTrans.naturality] }

Depends on / 依赖: Functor, Functor.map_id, NatTrans, NatTrans.id_app, NatTrans.naturality, comp_id, id_app, id_comp, mapBifunctorMapMap, mapBifunctorMapObj, mapMap_comp, map_id, naturality
-/
noncomputable def mapBifunctorMap [forall X Y, HasMap (((mapBifunctor F I J).obj X).obj Y) p] :
    GradedObject I C₁ ⥤ GradedObject J C₂ ⥤ GradedObject K C₃ where
  obj X :=
    { obj := fun Y => mapBifunctorMapObj F p X Y
      map := fun ψ => mapBifunctorMapMap F p (𝟙 X) ψ }
  map {X₁ X₂} φ :=
    { app := fun Y => mapBifunctorMapMap F p φ (𝟙 Y)
      naturality := fun {Y₁ Y₂} ψ => by
        dsimp
        simp only [Functor.map_id, NatTrans.id_app, id_comp, comp_id,
          ← mapMap_comp, NatTrans.naturality] }

end

end GradedObject

end CategoryTheory
