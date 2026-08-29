/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# Properties of objects in target categories of a pseudofunctor to `Cat`

Given `F : Pseudofunctor B Cat`, we introduce a type `F.ObjectProperty`
which consists of properties `P` of objects for all categories `F.obj X` for `X : B`.
The typeclass `P.IsClosedUnderMapObj` expresses that this property
is preserved by the application of the functors `F.map`: this allows
to define a sub-pseudofunctor `P.fullsubcategory : Pseudofunctor B Cat`.

## TODO (@joelriou)
* Given a Grothendieck topology `J` on a category `C`, define
  a type class `Pseudofunctor.ObjectProperty.IsLocal P J` extending
  `IsClosedUnderMapObj` saying that if an object locally satisfies
  the property, then it satisfies the property. Assuming this, show that
  `P.fullsubcategory` is a stack if the original pseudofunctor was.

-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

open Bicategory

namespace Pseudofunctor

variable {B : Type u} [Bicategory.{w, v} B] (F : Pseudofunctor B Cat.{v', u'})

/--
Definition of `ObjectProperty` / `ObjectProperty` 的定义

English:
structure ObjectProperty
  parameters: where
  axioms and operations (1):
    - prop((X : B)) : CategoryTheory.ObjectProperty (F.obj X)

中文:
结构 ObjectProperty
  参数: where
  公理与运算 (1 个):
    - prop((X : B)) : CategoryTheory.Object命题erty (F.obj X)
-/
protected structure ObjectProperty where
  /-- A property of objects in the category `F.obj X` for all `X : B`. -/
  prop (X : B) : CategoryTheory.ObjectProperty (F.obj X)

namespace ObjectProperty

variable {F} (P : F.ObjectProperty)

/--
Definition of `Obj` / `Obj` 的定义

English:
abbreviation Obj
  signature: (X : B)
  body: (P.prop X).FullSubcategory

中文:
缩写 Obj
  签名: (X : B)
  定义体: (P.prop X).FullSubcategory

Depends on / 依赖: FullSubcategory, P.prop
-/
abbrev Obj (X : B) := (P.prop X).FullSubcategory

/--
Definition of `IsClosedUnderMapObj` / `IsClosedUnderMapObj` 的定义

English:
class IsClosedUnderMapObj
  parameters: (P : F.ObjectProperty)
  axioms and operations (1):
    - map_obj((P) {X Y : B} {M : F.obj X} (hM : P.prop X M) (f : X ⟶ Y)) : P.prop Y ((F.map f).toFunctor.obj M)

中文:
类 IsClosedUnderMapObj
  参数: (P : F.Object命题erty)
  公理与运算 (1 个):
    - map_obj((P) {X Y : B} {M : F.obj X} (hM : P.prop X M) (f : X ⟶ Y)) : P.prop Y ((F.map f).toFunctor.obj M)
-/
class IsClosedUnderMapObj (P : F.ObjectProperty) : Prop where
  map_obj (P) {X Y : B} {M : F.obj X} (hM : P.prop X M) (f : X ⟶ Y) :
    P.prop Y ((F.map f).toFunctor.obj M)

export IsClosedUnderMapObj (map_obj)

/--
Definition of `IsClosedUnderIsomorphisms` / `IsClosedUnderIsomorphisms` 的定义

English:
class IsClosedUnderIsomorphisms
  parameters: : Prop where
  axioms and operations (1):
    - isClosedUnderIsomorphisms((X : B)) : (P.prop X).IsClosedUnderIsomorphisms

中文:
类 IsClosedUnderIsomorphisms
  参数: : 命题 where
  公理与运算 (1 个):
    - isClosedUnderIsomorphisms((X : B)) : (P.prop X).IsClosedUnderIsomorphisms
-/
class IsClosedUnderIsomorphisms : Prop where
  isClosedUnderIsomorphisms (X : B) : (P.prop X).IsClosedUnderIsomorphisms

attribute [instance] IsClosedUnderIsomorphisms.isClosedUnderIsomorphisms

section

variable [P.IsClosedUnderMapObj]

/-- Given a property `P` of objects for `F : Pseudofunctor B Cat` and a morphism `f : X ⟶ Y`
in `B`, this is the functor `P.Obj X ⥤ P.Obj Y` that is induced by `F.map f`. -/
@[simps!]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {X Y : B} (f : X ⟶ Y)
  body: (P.prop Y).lift (ObjectProperty.ι _ ⋙ (F.map f).toFunctor)
    (fun M => P.map_obj M.2 f)

中文:
定义 map
  签名: {X Y : B} (f : X ⟶ Y)
  定义体: (P.prop Y).lift (ObjectProperty.ι _ ⋙ (F.map f).toFunctor)
    (fun M => P.map_obj M.2 f)

Depends on / 依赖: F.map, ObjectProperty, P.map_obj, P.prop, map_obj, toFunctor
-/
def map {X Y : B} (f : X ⟶ Y) :
    P.Obj X ⥤ P.Obj Y :=
  (P.prop Y).lift (ObjectProperty.ι _ ⋙ (F.map f).toFunctor)
    (fun M => P.map_obj M.2 f)

/-- Given a property `P` of objects for `F : Pseudofunctor B Cat` and
a `2`-morphism in `B`, this is the induced natural transformation between
the induced functors on the fullsubcategories of objects satisfying `P`. -/
@[simps!]
/--
Definition of `map₂` / `map₂` 的定义

English:
definition map₂
  signature: {X Y : B} {f g : X ⟶ Y} (α : f ⟶ g)
  body: ((P.prop Y).fullyFaithfulι.whiskeringRight _).preimage
    (Functor.whiskerLeft (P.prop X).ι (F.map₂ α).toNatTrans)

中文:
定义 map₂
  签名: {X Y : B} {f g : X ⟶ Y} (α : f ⟶ g)
  定义体: ((P.prop Y).fullyFaithfulι.whiskeringRight _).preimage
    (Functor.whiskerLeft (P.prop X).ι (F.map₂ α).toNatTrans)

Depends on / 依赖: F.map, Functor, Functor.whiskerLeft, P.prop, preimage, toNatTrans, whiskerLeft, whiskeringRight
-/
def map₂ {X Y : B} {f g : X ⟶ Y} (α : f ⟶ g) :
    P.map f ⟶ P.map g :=
  ((P.prop Y).fullyFaithfulι.whiskeringRight _).preimage
    (Functor.whiskerLeft (P.prop X).ι (F.map₂ α).toNatTrans)

/--
Definition of `mapId` / `mapId` 的定义

English:
definition mapId
  signature: (X : B)
  body: ((P.prop X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (P.prop X).ι (Cat.Hom.toNatIso (F.mapId X)))

@[simp]

中文:
定义 mapId
  签名: (X : B)
  定义体: ((P.prop X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (P.prop X).ι (Cat.Hom.toNatIso (F.mapId X)))

@[simp]

Depends on / 依赖: Cat.Hom.toNatIso, F.mapId, Functor, Functor.isoWhiskerLeft, P.prop, isoWhiskerLeft, preimageIso, toNatIso, whiskeringRight
-/
def mapId (X : B) :
    P.map (𝟙 X) ≅ 𝟭 _ :=
  ((P.prop X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (P.prop X).ι (Cat.Hom.toNatIso (F.mapId X)))

@[simp]
/--
lemma `mapId_hom_app` / 引理 `mapId_hom_app`

English:
lemma mapId_hom_app
  given: {X : B} (M : P.Obj X)
  proof: rfl

@[simp]

中文:
引理 mapId_hom_app
  条件: {X : B} (M : P.Obj X)
  证明: rfl

@[simp]
-/
lemma mapId_hom_app {X : B} (M : P.Obj X) :
  (P.mapId X).hom.app M = ObjectProperty.homMk
    ((F.mapId X).hom.toNatTrans.app M.obj) := rfl

@[simp]
/--
lemma `mapId_inv_app` / 引理 `mapId_inv_app`

English:
lemma mapId_inv_app
  given: {X : B} (M : P.Obj X)
  proof: rfl

中文:
引理 mapId_inv_app
  条件: {X : B} (M : P.Obj X)
  证明: rfl
-/
lemma mapId_inv_app {X : B} (M : P.Obj X) :
  (P.mapId X).inv.app M = ObjectProperty.homMk
    ((F.mapId X).inv.toNatTrans.app M.obj) := rfl

/--
Definition of `mapComp` / `mapComp` 的定义

English:
definition mapComp
  signature: {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z)
  body: ((P.prop Z).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (P.prop X).ι (Cat.Hom.toNatIso (F.mapComp f g)))

@[simp]

中文:
定义 mapComp
  签名: {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z)
  定义体: ((P.prop Z).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (P.prop X).ι (Cat.Hom.toNatIso (F.mapComp f g)))

@[simp]

Depends on / 依赖: Cat.Hom.toNatIso, F.mapComp, Functor, Functor.isoWhiskerLeft, P.prop, isoWhiskerLeft, mapComp, preimageIso, toNatIso, whiskeringRight
-/
def mapComp {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    P.map (f ≫ g) ≅ P.map f ⋙ P.map g :=
  ((P.prop Z).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (P.prop X).ι (Cat.Hom.toNatIso (F.mapComp f g)))

@[simp]
/--
lemma `mapComp_hom_app` / 引理 `mapComp_hom_app`

English:
lemma mapComp_hom_app
  given: {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) (M : P.Obj X)
  proof: rfl

@[simp]

中文:
引理 mapComp_hom_app
  条件: {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) (M : P.Obj X)
  证明: rfl

@[simp]
-/
lemma mapComp_hom_app {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) (M : P.Obj X) :
    (P.mapComp f g).hom.app M = ObjectProperty.homMk
      ((F.mapComp f g).hom.toNatTrans.app M.obj) := rfl

@[simp]
/--
lemma `mapComp_inv_app` / 引理 `mapComp_inv_app`

English:
lemma mapComp_inv_app
  given: {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) (M : P.Obj X)
  proof: rfl

中文:
引理 mapComp_inv_app
  条件: {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) (M : P.Obj X)
  证明: rfl
-/
lemma mapComp_inv_app {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) (M : P.Obj X) :
    (P.mapComp f g).inv.app M = ObjectProperty.homMk
      ((F.mapComp f g).inv.toNatTrans.app M.obj) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Given a property of objects `P` for a pseudofunctor from `B` to `Cat`, this is
the induced pseudofunctor which sends `X : B` to the full subcategory of `F.obj X`
consisting of objects satisfying `P`. -/
@[simps]
/--
Definition of `fullsubcategory` / `fullsubcategory` 的定义

English:
definition fullsubcategory
  signature: : Pseudofunctor B Cat where
  body: Cat.of (P.Obj X)
  map f := Cat.Hom.ofFunctor (P.map f)
  map₂ α := Cat.Hom₂.ofNatTrans (P.map₂ α)
  mapId X := Cat.Hom.isoMk (P.mapId X)
  mapComp f g := Cat.Hom.isoMk (P.mapComp f g)

中文:
定义 fullsubcategory
  签名: : Pseudofunctor B Cat where
  定义体: Cat.of (P.Obj X)
  map f := Cat.Hom.ofFunctor (P.map f)
  map₂ α := Cat.Hom₂.ofNatTrans (P.map₂ α)
  mapId X := Cat.Hom.isoMk (P.mapId X)
  mapComp f g := Cat.Hom.isoMk (P.mapComp f g)

Depends on / 依赖: Cat.of, P.Obj
-/
def fullsubcategory : Pseudofunctor B Cat where
  obj X := Cat.of (P.Obj X)
  map f := Cat.Hom.ofFunctor (P.map f)
  map₂ α := Cat.Hom₂.ofNatTrans (P.map₂ α)
  mapId X := Cat.Hom.isoMk (P.mapId X)
  mapComp f g := Cat.Hom.isoMk (P.mapComp f g)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The inclusion of `P.fullsubcategory` in `F`. -/
@[simps]
/--
Definition of `ι` / `ι` 的定义

English:
definition ι
  signature: : StrongTrans P.fullsubcategory F where
  body: Cat.Hom.ofFunctor (P.prop (X := X)).ι
  naturality f := Iso.refl _

中文:
定义 ι
  签名: : StrongTrans P.fullsubcategory F where
  定义体: Cat.Hom.ofFunctor (P.prop (X := X)).ι
  naturality f := Iso.refl _

Depends on / 依赖: Cat.Hom.ofFunctor, P.prop, ofFunctor
-/
def ι : StrongTrans P.fullsubcategory F where
  app X := Cat.Hom.ofFunctor (P.prop (X := X)).ι
  naturality f := Iso.refl _

end

end ObjectProperty

end Pseudofunctor

end CategoryTheory
