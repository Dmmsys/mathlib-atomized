/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.CategoryTheory.Bicategory.Strict.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Bundled
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Category of categories

This file contains the definition of the category `Cat` of all categories.
In this category objects are categories and
morphisms are functors between these categories.

## Implementation notes

Though `Cat` is not a concrete category, we use `bundled` to define
its carrier type.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Bicategory CategoryTheory.Functor

-- intended to be used with explicit universe parameters
set_option linter.checkUnivs false in
/-- Category of categories. -/
@[implicit_reducible]
/--
Definition of `Cat` / `Cat` 的定义

English:
definition Cat
  body: Bundled Category.{v, u}

中文:
定义 Cat
  定义体: Bundled Category.{v, u}

Depends on / 依赖: Bundled, Category
-/
def Cat :=
  Bundled Category.{v, u}

namespace Cat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited Cat
  body: ⟨⟨Type u, CategoryTheory.types⟩⟩

中文:
实例 :
  签名: 可居 Cat
  定义体: ⟨⟨Type u, CategoryTheory.types⟩⟩

Depends on / 依赖: CategoryTheory, CategoryTheory.types
-/
instance : Inhabited Cat :=
  ⟨⟨Type u, CategoryTheory.types⟩⟩

-- TODO: maybe this coercion should be defined to be `objects.obj`?
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort Cat (Type u)
  body: ⟨Bundled.α⟩

中文:
实例 :
  签名: CoeSort Cat (类型u)
  定义体: ⟨Bundled.α⟩

Depends on / 依赖: Bundled
-/
instance : CoeSort Cat (Type u) :=
  ⟨Bundled.α⟩

/--
Instance `str` / 实例 `str`

English:
instance str
  signature: (C : Cat.{v, u})
  body: Bundled.str C

中文:
实例 str
  签名: (C : Cat.{v, u})
  定义体: Bundled.str C

Depends on / 依赖: Bundled, Bundled.str
-/
instance str (C : Cat.{v, u}) : Category.{v, u} C :=
  Bundled.str C

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (C : Type u) [Category.{v} C]
  body: Bundled.of C

中文:
定义 of
  签名: (C : 类型u) [范畴.{v} C]
  定义体: Bundled.of C

Depends on / 依赖: Bundled, Bundled.of, HasLimits, HasLimitsOfSize, hasSmallestLimitsOfHasLimits
-/
def of (C : Type u) [Category.{v} C] : Cat.{v, u} :=
  Bundled.of C

section

#adaptation_note /-- Removed `private`:
`ofFunctor` was marked `private` in #31807,
but we have removed this when disabling `set_option backward.privateInPublic` as a global option. -/
/--
The type of 1-morphisms in the bicategory of categories `Cat`.
This is a structure around `Functor` to prevent defeq-abuse
-/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (C D : Cat.{v, u})
  axioms and operations (2):
    - ofFunctor : :
    - toFunctor : C ⥤ D

中文:
结构 态射
  参数: (C D : Cat.{v, u})
  公理与运算 (2 个):
    - ofFunctor : :
    - toFunctor : C ⥤ D
-/
structure Hom (C D : Cat.{v, u}) where
  ofFunctor ::
  /-- The Functor underlying a 1-morphism in Cat -/
  toFunctor : C ⥤ D

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Quiver (Cat.{v, u})
  body: Hom C D

中文:
实例 :
  签名: 箭图 (Cat.{v, u})
  定义体: Hom C D
-/
instance : Quiver (Cat.{v, u}) where
  Hom C D := Hom C D

/-- The 1-morphism in `Cat` corresponding to a functor. -/
@[simps, implicit_reducible]
/--
Definition of `_root_.CategoryTheory.Functor.toCatHom` / `_root_.CategoryTheory.Functor.toCatHom` 的定义

English:
definition _root_.CategoryTheory.Functor.toCatHom
  signature: {C D : Type u} [Category.{v} C] [Category.{v} D]
  body: F

@[ext]

中文:
定义 _root_.范畴论.函子.toCatHom
  签名: {C D : 类型u} [范畴.{v} C] [范畴.{v} D]
  定义体: F

@[ext]
-/
def _root_.CategoryTheory.Functor.toCatHom {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) : Cat.of C ⟶ Cat.of D where
  toFunctor := F

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {C D : Cat.{v, u}} {F G : C ⟶ D} (h : F.toFunctor = G.toFunctor)
  statement: F = G
  proof: congrArg (Functor.toCatHom) h

中文:
引理 ext
  条件: {C D : Cat.{v, u}} {F G : C ⟶ D} (h : F.toFunctor = G.toFunctor)
  结论: F = G
  证明: congrArg (Functor.toCatHom) h

Depends on / 依赖: Functor, Functor.toCatHom, toCatHom
-/
lemma ext {C D : Cat.{v, u}} {F G : C ⟶ D} (h : F.toFunctor = G.toFunctor) : F = G :=
  congrArg (Functor.toCatHom) h

/--
The equivalence between the type of functors between two categories and
the type of 1-morphisms in Cat between the objects corresponding to those categories.
-/
@[simps]
/--
Definition of `_root_.CategoryTheory.Functor.equivCatHom` / `_root_.CategoryTheory.Functor.equivCatHom` 的定义

English:
definition _root_.CategoryTheory.Functor.equivCatHom
  signature: (C D : Type u) [Category.{v} C] [Category.{v} D]
  body: Functor.toCatHom
  invFun := Cat.Hom.toFunctor
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 _root_.范畴论.函子.equivCatHom
  签名: (C D : 类型u) [范畴.{v} C] [范畴.{v} D]
  定义体: Functor.toCatHom
  invFun := Cat.Hom.toFunctor
  left_inv _ := rfl
  right_inv _ := rfl

Depends on / 依赖: Functor, Functor.toCatHom, toCatHom
-/
def _root_.CategoryTheory.Functor.equivCatHom (C D : Type u) [Category.{v} C] [Category.{v} D] :
    C ⥤ D ≃ ((Cat.of C) ⟶ (Cat.of D)) where
  toFun := Functor.toCatHom
  invFun := Cat.Hom.toFunctor
  left_inv _ := rfl
  right_inv _ := rfl

/--
The equivalence between the type of 1-morphisms in Cat between two objects
and the type of functors between the categories corresponding to those objects.
-/
@[simps! apply symm_apply]
/--
Definition of `Hom.equivFunctor` / `Hom.equivFunctor` 的定义

English:
definition Hom.equivFunctor
  signature: (C D : Cat.{v, u})
  body: (equivCatHom _ _).symm

#adaptation_note /-- Removed `private`:
`ofNatTrans` was marked `private` in #31807,
but we have removed this when disabling `set_option backward.privateInPublic` as a global option. -/

中文:
定义 态射.equivFunctor
  签名: (C D : Cat.{v, u})
  定义体: (equivCatHom _ _).symm

#adaptation_note /-- Removed `private`:
`ofNatTrans` was marked `private` in #31807,
but we have removed this when disabling `set_option backward.privateInPublic` as a global option. -/

Depends on / 依赖: equivCatHom
-/
def Hom.equivFunctor (C D : Cat.{v, u}) :
    (C ⟶ D) ≃ C ⥤ D := (equivCatHom _ _).symm

#adaptation_note /-- Removed `private`:
`ofNatTrans` was marked `private` in #31807,
but we have removed this when disabling `set_option backward.privateInPublic` as a global option. -/
/--
Definition of `Hom₂` / `Hom₂` 的定义

English:
structure Hom₂
  parameters: {C D : Cat.{v, u}} (F G : C ⟶ D)
  axioms and operations (2):
    - ofNatTrans : :
    - toNatTrans : F.toFunctor ⟶ G.toFunctor

中文:
结构 Hom₂
  参数: {C D : Cat.{v, u}} (F G : C ⟶ D)
  公理与运算 (2 个):
    - ofNatTrans : :
    - toNatTrans : F.toFunctor ⟶ G.toFunctor
-/
structure Hom₂ {C D : Cat.{v, u}} (F G : C ⟶ D) where
  ofNatTrans ::
  /-- The natural transformation underlying a 2-morphism in `Cat` -/
  toNatTrans : F.toFunctor ⟶ G.toFunctor

namespace Hom

/--
Instance `instQuiver` / 实例 `instQuiver`

English:
instance instQuiver
  signature: {C D : Cat.{v, u}}
  body: Hom₂ F G

中文:
实例 instQuiver
  签名: {C D : Cat.{v, u}}
  定义体: Hom₂ F G
-/
instance instQuiver {C D : Cat.{v, u}} : Quiver (C ⟶ D) where
  Hom F G := Hom₂ F G

/-- The 2-morphism in `Cat` corresponding to a natural transformation between functors. -/
@[simps]
/--
Definition of `_root_.CategoryTheory.NatTrans.toCatHom₂` / `_root_.CategoryTheory.NatTrans.toCatHom₂` 的定义

English:
definition _root_.CategoryTheory.NatTrans.toCatHom₂
  signature: {C D : Type u} [Category.{v} C]
  body: η

中文:
定义 _root_.范畴论.自然变换.toCatHom₂
  签名: {C D : 类型u} [范畴.{v} C]
  定义体: η
-/
def _root_.CategoryTheory.NatTrans.toCatHom₂ {C D : Type u} [Category.{v} C]
    [Category.{v} D] {F G : C ⥤ D} (η : F ⟶ G) : F.toCatHom ⟶ G.toCatHom where
  toNatTrans := η

/--
Instance `instCategory` / 实例 `instCategory`

English:
instance instCategory
  signature: {X Y : Cat.{v, u}}
  body: NatTrans.toCatHom₂ (𝟙 F.toFunctor)
  comp η₁ η₂ := NatTrans.toCatHom₂ (η₁.toNatTrans ≫ η₂.toNatTrans)
  id_comp η := congrArg (NatTrans.toCatHom₂) (Category.id_comp η.toNatTrans)
  comp_id η := congrArg (NatTrans.toCatHom₂) (Category.comp_id η.toNatTrans)
  assoc η₁ η₂ η₃ :=
    congrArg (NatTrans.t

中文:
实例 instCategory
  签名: {X Y : Cat.{v, u}}
  定义体: NatTrans.toCatHom₂ (𝟙 F.toFunctor)
  comp η₁ η₂ := NatTrans.toCatHom₂ (η₁.toNatTrans ≫ η₂.toNatTrans)
  id_comp η := congrArg (NatTrans.toCatHom₂) (Category.id_comp η.toNatTrans)
  comp_id η := congrArg (NatTrans.toCatHom₂) (Category.comp_id η.toNatTrans)
  assoc η₁ η₂ η₃ :=
    congrArg (NatTrans.t

Depends on / 依赖: F.toFunctor, NatTrans, NatTrans.toCatHom, toFunctor
-/
instance instCategory {X Y : Cat.{v, u}} : Category (X ⟶ Y) where
  id F := NatTrans.toCatHom₂ (𝟙 F.toFunctor)
  comp η₁ η₂ := NatTrans.toCatHom₂ (η₁.toNatTrans ≫ η₂.toNatTrans)
  id_comp η := congrArg (NatTrans.toCatHom₂) (Category.id_comp η.toNatTrans)
  comp_id η := congrArg (NatTrans.toCatHom₂) (Category.comp_id η.toNatTrans)
  assoc η₁ η₂ η₃ :=
    congrArg (NatTrans.toCatHom₂) (Category.assoc η₁.toNatTrans η₂.toNatTrans η₃.toNatTrans)

@[simp, push_cast]
/--
lemma `_root_.CategoryTheory.NatTrans.toCatHom₂_id` / 引理 `_root_.CategoryTheory.NatTrans.toCatHom₂_id`

English:
lemma _root_.CategoryTheory.NatTrans.toCatHom₂_id
  statement: {C D : Type u} [Category.{v} C] [Category.{v} D]
  proof: rfl

@[simp, push_cast]

中文:
引理 _root_.范畴论.自然变换.toCatHom₂_id
  结论: {C D : 类型u} [范畴.{v} C] [范畴.{v} D]
  证明: rfl

@[simp, push_cast]
-/
lemma _root_.CategoryTheory.NatTrans.toCatHom₂_id {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) :
    (𝟙 F : F ⟶ F).toCatHom₂ = 𝟙 F.toCatHom := rfl

@[simp, push_cast]
/--
lemma `_root_.CategoryTheory.NatTrans.toCatHom₂_comp` / 引理 `_root_.CategoryTheory.NatTrans.toCatHom₂_comp`

English:
lemma _root_.CategoryTheory.NatTrans.toCatHom₂_comp
  statement: {C D : Type u} [Category.{v} C] [Category.{v} D]
  proof: rfl

@[simp, push_cast]

中文:
引理 _root_.范畴论.自然变换.toCatHom₂_comp
  结论: {C D : 类型u} [范畴.{v} C] [范畴.{v} D]
  证明: rfl

@[simp, push_cast]
-/
lemma _root_.CategoryTheory.NatTrans.toCatHom₂_comp {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G H : C ⥤ D} (η₁ : F ⟶ G) (η₂ : G ⟶ H) :
    (η₁ ≫ η₂).toCatHom₂ = η₁.toCatHom₂ ≫ η₂.toCatHom₂ := rfl

@[simp, push_cast]
/--
lemma `toNatTrans_id` / 引理 `toNatTrans_id`

English:
lemma toNatTrans_id
  given: {C D : Cat.{v, u}} (F : C ⟶ D)
  proof: rfl

@[simp, push_cast]

中文:
引理 to自然数Trans_id
  条件: {C D : Cat.{v, u}} (F : C ⟶ D)
  证明: rfl

@[simp, push_cast]
-/
lemma toNatTrans_id {C D : Cat.{v, u}} (F : C ⟶ D) :
  (𝟙 F : F ⟶ F).toNatTrans = 𝟙 (F.toFunctor) := rfl

@[simp, push_cast]
/--
lemma `toNatTrans_comp` / 引理 `toNatTrans_comp`

English:
lemma toNatTrans_comp
  given: {C D : Cat.{v, u}} {F G H : C ⟶ D} (η₁ : F ⟶ G) (η₂ : G ⟶ H)
  proof: rfl

@[ext]

中文:
引理 to自然数Trans_comp
  条件: {C D : Cat.{v, u}} {F G H : C ⟶ D} (η₁ : F ⟶ G) (η₂ : G ⟶ H)
  证明: rfl

@[ext]
-/
lemma toNatTrans_comp {C D : Cat.{v, u}} {F G H : C ⟶ D} (η₁ : F ⟶ G) (η₂ : G ⟶ H) :
  (η₁ ≫ η₂).toNatTrans = η₁.toNatTrans ≫ η₂.toNatTrans := rfl

@[ext]
/--
lemma `_root_.CategoryTheory.Cat.Hom₂.ext` / 引理 `_root_.CategoryTheory.Cat.Hom₂.ext`

English:
lemma _root_.CategoryTheory.Cat.Hom₂.ext
  statement: {C D : Cat.{v, u}} {F G : C ⟶ D} {η₁ η₂ : F ⟶ G}
  proof: congr($(h).toCatHom₂)

中文:
引理 _root_.范畴论.Cat.Hom₂.ext
  结论: {C D : Cat.{v, u}} {F G : C ⟶ D} {η₁ η₂ : F ⟶ G}
  证明: congr($(h).toCatHom₂)
-/
lemma _root_.CategoryTheory.Cat.Hom₂.ext {C D : Cat.{v, u}} {F G : C ⟶ D} {η₁ η₂ : F ⟶ G}
    (h : η₁.toNatTrans = η₂.toNatTrans) : η₁ = η₂ := congr($(h).toCatHom₂)

/-- The 2-iso in Cat corresponding to a natural isomorphism. -/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {C D : Type u} [Category.{v} C] [Category.{v} D] {F G : C ⥤ D} (e : F ≅ G)
  body: e.hom.toCatHom₂
  inv := e.inv.toCatHom₂
  hom_inv_id := congrArg NatTrans.toCatHom₂ e.hom_inv_id
  inv_hom_id := congrArg NatTrans.toCatHom₂ e.inv_hom_id

中文:
定义 isoMk
  签名: {C D : 类型u} [范畴.{v} C] [范畴.{v} D] {F G : C ⥤ D} (e : F ≅ G)
  定义体: e.hom.toCatHom₂
  inv := e.inv.toCatHom₂
  hom_inv_id := congrArg NatTrans.toCatHom₂ e.hom_inv_id
  inv_hom_id := congrArg NatTrans.toCatHom₂ e.inv_hom_id

Depends on / 依赖: e.hom.toCatHom
-/
def isoMk {C D : Type u} [Category.{v} C] [Category.{v} D] {F G : C ⥤ D} (e : F ≅ G) :
    F.toCatHom ≅ G.toCatHom where
  hom := e.hom.toCatHom₂
  inv := e.inv.toCatHom₂
  hom_inv_id := congrArg NatTrans.toCatHom₂ e.hom_inv_id
  inv_hom_id := congrArg NatTrans.toCatHom₂ e.inv_hom_id

/-- The natural isomorphism corresponding to a 2-iso in `Cat` -/
@[simps]
/--
Definition of `toNatIso` / `toNatIso` 的定义

English:
definition toNatIso
  signature: {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G)
  body: e.hom.toNatTrans
  inv := e.inv.toNatTrans
  hom_inv_id := congrArg Hom₂.toNatTrans e.hom_inv_id
  inv_hom_id := congrArg Hom₂.toNatTrans e.inv_hom_id

@[simp]

中文:
定义 to自然数Iso
  签名: {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G)
  定义体: e.hom.toNatTrans
  inv := e.inv.toNatTrans
  hom_inv_id := congrArg Hom₂.toNatTrans e.hom_inv_id
  inv_hom_id := congrArg Hom₂.toNatTrans e.inv_hom_id

@[simp]

Depends on / 依赖: e.hom.toNatTrans, toNatTrans
-/
def toNatIso {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) : F.toFunctor ≅ G.toFunctor where
  hom := e.hom.toNatTrans
  inv := e.inv.toNatTrans
  hom_inv_id := congrArg Hom₂.toNatTrans e.hom_inv_id
  inv_hom_id := congrArg Hom₂.toNatTrans e.inv_hom_id

@[simp]
/--
lemma `isoMk_toNatIso` / 引理 `isoMk_toNatIso`

English:
lemma isoMk_toNatIso
  given: {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G)
  proof: rfl

@[simp]

中文:
引理 isoMk_to自然数Iso
  条件: {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G)
  证明: rfl

@[simp]
-/
lemma isoMk_toNatIso {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) :
    isoMk (Hom.toNatIso e) = e := rfl

@[simp]
/--
lemma `toNatIso_isoMk` / 引理 `toNatIso_isoMk`

English:
lemma toNatIso_isoMk
  given: {C D : Type u} [Category.{v} C] [Category.{v} D] {F G : C ⥤ D} (e : F ≅ G)
  proof: rfl

中文:
引理 to自然数Iso_isoMk
  条件: {C D : 类型u} [范畴.{v} C] [范畴.{v} D] {F G : C ⥤ D} (e : F ≅ G)
  证明: rfl
-/
lemma toNatIso_isoMk {C D : Type u} [Category.{v} C] [Category.{v} D] {F G : C ⥤ D} (e : F ≅ G) :
    Hom.toNatIso (isoMk e) = e := rfl

instance {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) :
    IsIso e.hom.toNatTrans :=
  (toNatIso e).isIso_hom

instance {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) :
    IsIso e.inv.toNatTrans :=
  (toNatIso e).isIso_inv

@[reassoc (attr := simp)]
/--
lemma `hom_inv_id_toNatTrans` / 引理 `hom_inv_id_toNatTrans`

English:
lemma hom_inv_id_toNatTrans
  given: {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G)
  proof: (toNatIso e).hom_inv_id

@[reassoc (attr := simp)]

中文:
引理 hom_inv_id_to自然数Trans
  条件: {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G)
  证明: (toNatIso e).hom_inv_id

@[reassoc (attr := simp)]

Depends on / 依赖: hom_inv_id, toNatIso
-/
lemma hom_inv_id_toNatTrans {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) :
    e.hom.toNatTrans ≫ e.inv.toNatTrans = 𝟙 _ :=
  (toNatIso e).hom_inv_id

@[reassoc (attr := simp)]
/--
lemma `inv_hom_id_toNatTrans` / 引理 `inv_hom_id_toNatTrans`

English:
lemma inv_hom_id_toNatTrans
  given: {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G)
  proof: (toNatIso e).inv_hom_id

@[reassoc (attr := simp)]

中文:
引理 inv_hom_id_to自然数Trans
  条件: {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G)
  证明: (toNatIso e).inv_hom_id

@[reassoc (attr := simp)]

Depends on / 依赖: inv_hom_id, toNatIso
-/
lemma inv_hom_id_toNatTrans {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) :
    e.inv.toNatTrans ≫ e.hom.toNatTrans = 𝟙 _ :=
  (toNatIso e).inv_hom_id

@[reassoc (attr := simp)]
/--
lemma `hom_inv_id_toNatTrans_app` / 引理 `hom_inv_id_toNatTrans_app`

English:
lemma hom_inv_id_toNatTrans_app
  given: {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) (A : X)
  proof: (toNatIso e).hom_inv_id_app A

@[reassoc (attr := simp)]

中文:
引理 hom_inv_id_to自然数Trans_app
  条件: {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) (A : X)
  证明: (toNatIso e).hom_inv_id_app A

@[reassoc (attr := simp)]

Depends on / 依赖: hom_inv_id_app, toNatIso
-/
lemma hom_inv_id_toNatTrans_app {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) (A : X) :
    e.hom.toNatTrans.app A ≫ e.inv.toNatTrans.app A = 𝟙 _ :=
  (toNatIso e).hom_inv_id_app A

@[reassoc (attr := simp)]
/--
lemma `inv_hom_id_toNatTrans_app` / 引理 `inv_hom_id_toNatTrans_app`

English:
lemma inv_hom_id_toNatTrans_app
  given: {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) (A : X)
  proof: (toNatIso e).inv_hom_id_app A

中文:
引理 inv_hom_id_to自然数Trans_app
  条件: {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) (A : X)
  证明: (toNatIso e).inv_hom_id_app A

Depends on / 依赖: inv_hom_id_app, toNatIso
-/
lemma inv_hom_id_toNatTrans_app {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) (A : X) :
    e.inv.toNatTrans.app A ≫ e.hom.toNatTrans.app A = 𝟙 _ :=
  (toNatIso e).inv_hom_id_app A

end Hom

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `bicategory` / 实例 `bicategory`

English:
instance bicategory
  signature: : Bicategory.{max v u, max v u} Cat.{v, u} where
  body: (𝟭 C).toCatHom
  comp F G := (F.toFunctor ⋙ G.toFunctor).toCatHom
  homCategory := fun _ _ => Hom.instCategory
  whiskerLeft F _ _ η := (Functor.whiskerLeft F.toFunctor η.toNatTrans).toCatHom₂
  whiskerRight η H := (Functor.whiskerRight η.toNatTrans H.toFunctor).toCatHom₂
  associator F G H := Hom.i

中文:
实例 bicategory
  签名: : 双范畴.{最大值 v u, 最大值 v u} Cat.{v, u} where
  定义体: (𝟭 C).toCatHom
  comp F G := (F.toFunctor ⋙ G.toFunctor).toCatHom
  homCategory := fun _ _ => Hom.instCategory
  whiskerLeft F _ _ η := (Functor.whiskerLeft F.toFunctor η.toNatTrans).toCatHom₂
  whiskerRight η H := (Functor.whiskerRight η.toNatTrans H.toFunctor).toCatHom₂
  associator F G H := Hom.i

Depends on / 依赖: toCatHom
-/
instance bicategory : Bicategory.{max v u, max v u} Cat.{v, u} where
  id C := (𝟭 C).toCatHom
  comp F G := (F.toFunctor ⋙ G.toFunctor).toCatHom
  homCategory := fun _ _ => Hom.instCategory
  whiskerLeft F _ _ η := (Functor.whiskerLeft F.toFunctor η.toNatTrans).toCatHom₂
  whiskerRight η H := (Functor.whiskerRight η.toNatTrans H.toFunctor).toCatHom₂
  associator F G H := Hom.isoMk
    (Functor.associator F.toFunctor G.toFunctor H.toFunctor)
  leftUnitor F := Hom.isoMk (Functor.leftUnitor F.toFunctor)
  rightUnitor F := Hom.isoMk (Functor.rightUnitor F.toFunctor)

/--
Instance `bicategory.strict` / 实例 `bicategory.strict`

English:
instance bicategory.strict
  signature: : Bicategory.Strict Cat.{v, u} where
  body: by cases F; rfl
  comp_id {C} {D} F := by cases F; rfl
  assoc := by intros; rfl

中文:
实例 bicategory.strict
  签名: : 双范畴.Strict Cat.{v, u} where
  定义体: by cases F; rfl
  comp_id {C} {D} F := by cases F; rfl
  assoc := by intros; rfl

Depends on / 依赖: comp_id, intros
-/
instance bicategory.strict : Bicategory.Strict Cat.{v, u} where
  id_comp {C} {D} F := by cases F; rfl
  comp_id {C} {D} F := by cases F; rfl
  assoc := by intros; rfl

/--
Instance `category` / 实例 `category`

English:
instance category
  signature: : LargeCategory.{max v u} Cat.{v, u}
  body: StrictBicategory.category Cat.{v, u}

@[simp, push_cast]

中文:
实例 category
  签名: : 大范畴.{最大值 v u} Cat.{v, u}
  定义体: StrictBicategory.category Cat.{v, u}

@[simp, push_cast]

Depends on / 依赖: StrictBicategory, StrictBicategory.category, category
-/
instance category : LargeCategory.{max v u} Cat.{v, u} :=
  StrictBicategory.category Cat.{v, u}

@[simp, push_cast]
/--
lemma `Hom.id_toFunctor` / 引理 `Hom.id_toFunctor`

English:
lemma Hom.id_toFunctor
  given: {C : Cat.{v, u}}
  statement: (𝟙 C : C ⟶ C).toFunctor = 𝟭 C
  proof: rfl

@[simp]

中文:
引理 态射.id_toFunctor
  条件: {C : Cat.{v, u}}
  结论: (𝟙 C : C ⟶ C).toFunctor = 𝟭 C
  证明: rfl

@[simp]
-/
lemma Hom.id_toFunctor {C : Cat.{v, u}} : (𝟙 C : C ⟶ C).toFunctor = 𝟭 C := rfl

@[simp]
/--
theorem `Hom.id_obj` / 定理 `Hom.id_obj`

English:
theorem Hom.id_obj
  given: {C : Cat.{v, u}} (X : C)
  statement: (𝟙 C : C ⟶ C).toFunctor.obj X = X
  proof: by
  simp

@[simp]

中文:
定理 态射.id_obj
  条件: {C : Cat.{v, u}} (X : C)
  结论: (𝟙 C : C ⟶ C).toFunctor.obj X = X
  证明: by
  simp

@[simp]
-/
theorem Hom.id_obj {C : Cat.{v, u}} (X : C) : (𝟙 C : C ⟶ C).toFunctor.obj X = X := by
  simp

@[simp]
/--
theorem `Hom.id_map` / 定理 `Hom.id_map`

English:
theorem Hom.id_map
  given: {C : Cat.{v, u}} {X Y : C} (f : X ⟶ Y)
  statement: (𝟙 C : C ⟶ C).toFunctor.map f = f
  proof: by
  simp

@[simp, push_cast]

中文:
定理 态射.id_map
  条件: {C : Cat.{v, u}} {X Y : C} (f : X ⟶ Y)
  结论: (𝟙 C : C ⟶ C).toFunctor.map f = f
  证明: by
  simp

@[simp, push_cast]
-/
theorem Hom.id_map {C : Cat.{v, u}} {X Y : C} (f : X ⟶ Y) : (𝟙 C : C ⟶ C).toFunctor.map f = f := by
  simp

@[simp, push_cast]
/--
lemma `Hom.comp_toFunctor` / 引理 `Hom.comp_toFunctor`

English:
lemma Hom.comp_toFunctor
  given: {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E)
  proof: rfl

中文:
引理 态射.comp_toFunctor
  条件: {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E)
  证明: rfl
-/
lemma Hom.comp_toFunctor {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) :
  (F ≫ G).toFunctor = F.toFunctor ⋙ G.toFunctor := rfl

/--
theorem `Hom.comp_obj` / 定理 `Hom.comp_obj`

English:
theorem Hom.comp_obj
  given: {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) (X : C)
  proof: by
  simp

@[simp]

中文:
定理 态射.comp_obj
  条件: {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) (X : C)
  证明: by
  simp

@[simp]
-/
theorem Hom.comp_obj {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) (X : C) :
    (F ≫ G).toFunctor.obj X = G.toFunctor.obj (F.toFunctor.obj X) := by
  simp

@[simp]
/--
theorem `Hom.comp_map` / 定理 `Hom.comp_map`

English:
theorem Hom.comp_map
  given: {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) {X Y : C} (f : X ⟶ Y)
  proof: by
  simp

@[simp]

中文:
定理 态射.comp_map
  条件: {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) {X Y : C} (f : X ⟶ Y)
  证明: by
  simp

@[simp]
-/
theorem Hom.comp_map {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) {X Y : C} (f : X ⟶ Y) :
    (F ≫ G).toFunctor.map f = G.toFunctor.map (F.toFunctor.map f) := by
  simp

@[simp]
/--
theorem `Hom₂.id_app` / 定理 `Hom₂.id_app`

English:
theorem Hom₂.id_app
  given: {C D : Cat.{v, u}} (F : C ⟶ D) (X : C)
  proof: by
  simp

@[simp, reassoc]

中文:
定理 Hom₂.id_app
  条件: {C D : Cat.{v, u}} (F : C ⟶ D) (X : C)
  证明: by
  simp

@[simp, reassoc]
-/
theorem Hom₂.id_app {C D : Cat.{v, u}} (F : C ⟶ D) (X : C) :
    (𝟙 F : F ⟶ F).toNatTrans.app X = 𝟙 (F.toFunctor.obj X) := by
  simp

@[simp, reassoc]
/--
theorem `Hom₂.comp_app` / 定理 `Hom₂.comp_app`

English:
theorem Hom₂.comp_app
  given: {C D : Cat.{v, u}} {F G H : C ⟶ D} (α : F ⟶ G) (β : G ⟶ H) (X : C)
  proof: rfl

@[simp]

中文:
定理 Hom₂.comp_app
  条件: {C D : Cat.{v, u}} {F G H : C ⟶ D} (α : F ⟶ G) (β : G ⟶ H) (X : C)
  证明: rfl

@[simp]
-/
theorem Hom₂.comp_app {C D : Cat.{v, u}} {F G H : C ⟶ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) :
    (α ≫ β).toNatTrans.app X = α.toNatTrans.app X ≫ β.toNatTrans.app X := rfl

@[simp]
/--
theorem `Hom₂.eqToHom_toNatTrans` / 定理 `Hom₂.eqToHom_toNatTrans`

English:
theorem Hom₂.eqToHom_toNatTrans
  given: {C D : Cat.{v, u}} {F G : C ⟶ D} (h : F = G)
  proof: by cases h; simp

中文:
定理 Hom₂.eqToHom_to自然数Trans
  条件: {C D : Cat.{v, u}} {F G : C ⟶ D} (h : F = G)
  证明: by cases h; simp
-/
theorem Hom₂.eqToHom_toNatTrans {C D : Cat.{v, u}} {F G : C ⟶ D} (h : F = G) :
  (eqToHom h).toNatTrans = eqToHom congr(($h).toFunctor) := by cases h; simp

/--
theorem `eqToHom_app` / 定理 `eqToHom_app`

English:
theorem eqToHom_app
  given: {C D : Cat.{v, u}} (F G : C ⟶ D) (h : F = G) (X : C)
  proof: by
  simp

@[simp, push_cast]

中文:
定理 eqToHom_app
  条件: {C D : Cat.{v, u}} (F G : C ⟶ D) (h : F = G) (X : C)
  证明: by
  simp

@[simp, push_cast]
-/
theorem eqToHom_app {C D : Cat.{v, u}} (F G : C ⟶ D) (h : F = G) (X : C) :
    (eqToHom h).toNatTrans.app X = eqToHom congr(($h).toFunctor.obj X) := by
  simp

@[simp, push_cast]
/--
lemma `whiskerLeft_toNatTrans` / 引理 `whiskerLeft_toNatTrans`

English:
lemma whiskerLeft_toNatTrans
  given: {C D E : Cat.{v, u}} (F : C ⟶ D) {G H : D ⟶ E} (η : G ⟶ H)
  proof: rfl

中文:
引理 whiskerLeft_to自然数Trans
  条件: {C D E : Cat.{v, u}} (F : C ⟶ D) {G H : D ⟶ E} (η : G ⟶ H)
  证明: rfl
-/
lemma whiskerLeft_toNatTrans {C D E : Cat.{v, u}} (F : C ⟶ D) {G H : D ⟶ E} (η : G ⟶ H) :
  (F ◁ η).toNatTrans = F.toFunctor.whiskerLeft η.toNatTrans := rfl

/--
lemma `whiskerLeft_app` / 引理 `whiskerLeft_app`

English:
lemma whiskerLeft_app
  given: {C D E : Cat.{v, u}} (F : C ⟶ D) {G H : D ⟶ E} (η : G ⟶ H) (X : C)
  proof: by simp

@[simp, push_cast]

中文:
引理 whiskerLeft_app
  条件: {C D E : Cat.{v, u}} (F : C ⟶ D) {G H : D ⟶ E} (η : G ⟶ H) (X : C)
  证明: by simp

@[simp, push_cast]
-/
lemma whiskerLeft_app {C D E : Cat.{v, u}} (F : C ⟶ D) {G H : D ⟶ E} (η : G ⟶ H) (X : C) :
    (F ◁ η).toNatTrans.app X = η.toNatTrans.app (F.toFunctor.obj X) := by simp

@[simp, push_cast]
/--
lemma `whiskerRight_toNatTrans` / 引理 `whiskerRight_toNatTrans`

English:
lemma whiskerRight_toNatTrans
  given: {C D E : Cat.{v, u}} {F G : C ⟶ D} (H : D ⟶ E) (η : F ⟶ G)
  proof: rfl

中文:
引理 whiskerRight_to自然数Trans
  条件: {C D E : Cat.{v, u}} {F G : C ⟶ D} (H : D ⟶ E) (η : F ⟶ G)
  证明: rfl
-/
lemma whiskerRight_toNatTrans {C D E : Cat.{v, u}} {F G : C ⟶ D} (H : D ⟶ E) (η : F ⟶ G) :
    (η ▷ H).toNatTrans = Functor.whiskerRight η.toNatTrans H.toFunctor := rfl

/--
lemma `whiskerRight_app` / 引理 `whiskerRight_app`

English:
lemma whiskerRight_app
  given: {C D E : Cat.{v, u}} {F G : C ⟶ D} (H : D ⟶ E) (η : F ⟶ G) (X : C)
  proof: by simp

@[simp, push_cast]

中文:
引理 whiskerRight_app
  条件: {C D E : Cat.{v, u}} {F G : C ⟶ D} (H : D ⟶ E) (η : F ⟶ G) (X : C)
  证明: by simp

@[simp, push_cast]
-/
lemma whiskerRight_app {C D E : Cat.{v, u}} {F G : C ⟶ D} (H : D ⟶ E) (η : F ⟶ G) (X : C) :
    (η ▷ H).toNatTrans.app X = H.toFunctor.map (η.toNatTrans.app X) := by simp

@[simp, push_cast]
/--
lemma `Hom.toNatIso_leftUnitor` / 引理 `Hom.toNatIso_leftUnitor`

English:
lemma Hom.toNatIso_leftUnitor
  given: {B C : Cat.{v, u}} (F : B ⟶ C)
  proof: rfl

@[simp, push_cast]

中文:
引理 态射.to自然数Iso_leftUnitor
  条件: {B C : Cat.{v, u}} (F : B ⟶ C)
  证明: rfl

@[simp, push_cast]
-/
lemma Hom.toNatIso_leftUnitor {B C : Cat.{v, u}} (F : B ⟶ C) :
    Hom.toNatIso (fun_ F) = F.toFunctor.leftUnitor := rfl

@[simp, push_cast]
/--
lemma `leftUnitor_hom_toNatTrans` / 引理 `leftUnitor_hom_toNatTrans`

English:
lemma leftUnitor_hom_toNatTrans
  given: {B C : Cat.{v, u}} (F : B ⟶ C)
  proof: rfl

@[simp, push_cast]

中文:
引理 leftUnitor_hom_to自然数Trans
  条件: {B C : Cat.{v, u}} (F : B ⟶ C)
  证明: rfl

@[simp, push_cast]
-/
lemma leftUnitor_hom_toNatTrans {B C : Cat.{v, u}} (F : B ⟶ C) :
    (fun_ F).hom.toNatTrans = (F.toFunctor.leftUnitor).hom := rfl

@[simp, push_cast]
/--
lemma `leftUnitor_inv_toNatTrans` / 引理 `leftUnitor_inv_toNatTrans`

English:
lemma leftUnitor_inv_toNatTrans
  given: {B C : Cat.{v, u}} (F : B ⟶ C)
  proof: rfl

中文:
引理 leftUnitor_inv_to自然数Trans
  条件: {B C : Cat.{v, u}} (F : B ⟶ C)
  证明: rfl
-/
lemma leftUnitor_inv_toNatTrans {B C : Cat.{v, u}} (F : B ⟶ C) :
    (fun_ F).inv.toNatTrans = (F.toFunctor.leftUnitor).inv := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `leftUnitor_hom_app` / 引理 `leftUnitor_hom_app`

English:
lemma leftUnitor_hom_app
  given: {B C : Cat} (F : B ⟶ C) (X : B)
  proof: by simp

中文:
引理 leftUnitor_hom_app
  条件: {B C : Cat} (F : B ⟶ C) (X : B)
  证明: by simp
-/
lemma leftUnitor_hom_app {B C : Cat} (F : B ⟶ C) (X : B) :
    (fun_ F).hom.toNatTrans.app X = eqToHom (by simp) := by simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `leftUnitor_inv_app` / 引理 `leftUnitor_inv_app`

English:
lemma leftUnitor_inv_app
  given: {B C : Cat} (F : B ⟶ C) (X : B)
  proof: by simp

@[simp, push_cast]

中文:
引理 leftUnitor_inv_app
  条件: {B C : Cat} (F : B ⟶ C) (X : B)
  证明: by simp

@[simp, push_cast]
-/
lemma leftUnitor_inv_app {B C : Cat} (F : B ⟶ C) (X : B) :
    (fun_ F).inv.toNatTrans.app X = eqToHom (by simp) := by simp

@[simp, push_cast]
/--
lemma `Hom.toNatIso_rightUnitor` / 引理 `Hom.toNatIso_rightUnitor`

English:
lemma Hom.toNatIso_rightUnitor
  given: {B C : Cat.{v, u}} (F : B ⟶ C)
  proof: by simp; rfl

@[simp, push_cast]

中文:
引理 态射.to自然数Iso_rightUnitor
  条件: {B C : Cat.{v, u}} (F : B ⟶ C)
  证明: by simp; rfl

@[simp, push_cast]

Depends on / 依赖: HasColimits, hasSmallestColimitsOfHasColimits
-/
lemma Hom.toNatIso_rightUnitor {B C : Cat.{v, u}} (F : B ⟶ C) :
    Hom.toNatIso (ρ_ F) = eqToIso rfl ≪≫ F.toFunctor.rightUnitor ≪≫ eqToIso rfl := by simp; rfl

@[simp, push_cast]
/--
lemma `rightUnitor_hom_toNatTrans` / 引理 `rightUnitor_hom_toNatTrans`

English:
lemma rightUnitor_hom_toNatTrans
  given: {B C : Cat.{v, u}} (F : B ⟶ C)
  proof: rfl

@[simp, push_cast]

中文:
引理 rightUnitor_hom_to自然数Trans
  条件: {B C : Cat.{v, u}} (F : B ⟶ C)
  证明: rfl

@[simp, push_cast]
-/
lemma rightUnitor_hom_toNatTrans {B C : Cat.{v, u}} (F : B ⟶ C) :
    (ρ_ F).hom.toNatTrans = (F.toFunctor.rightUnitor).hom := rfl

@[simp, push_cast]
/--
lemma `rightUnitor_inv_toNatTrans` / 引理 `rightUnitor_inv_toNatTrans`

English:
lemma rightUnitor_inv_toNatTrans
  given: {B C : Cat.{v, u}} (F : B ⟶ C)
  proof: rfl

中文:
引理 rightUnitor_inv_to自然数Trans
  条件: {B C : Cat.{v, u}} (F : B ⟶ C)
  证明: rfl
-/
lemma rightUnitor_inv_toNatTrans {B C : Cat.{v, u}} (F : B ⟶ C) :
    (ρ_ F).inv.toNatTrans = (F.toFunctor.rightUnitor).inv := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `rightUnitor_hom_app` / 引理 `rightUnitor_hom_app`

English:
lemma rightUnitor_hom_app
  given: {B C : Cat.{v, u}} (F : B ⟶ C) (X : B)
  proof: by simp

中文:
引理 rightUnitor_hom_app
  条件: {B C : Cat.{v, u}} (F : B ⟶ C) (X : B)
  证明: by simp
-/
lemma rightUnitor_hom_app {B C : Cat.{v, u}} (F : B ⟶ C) (X : B) :
    (ρ_ F).hom.toNatTrans.app X = eqToHom (by simp) := by simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `rightUnitor_inv_app` / 引理 `rightUnitor_inv_app`

English:
lemma rightUnitor_inv_app
  given: {B C : Cat.{v, u}} (F : B ⟶ C) (X : B)
  proof: by simp

@[simp, push_cast]

中文:
引理 rightUnitor_inv_app
  条件: {B C : Cat.{v, u}} (F : B ⟶ C) (X : B)
  证明: by simp

@[simp, push_cast]
-/
lemma rightUnitor_inv_app {B C : Cat.{v, u}} (F : B ⟶ C) (X : B) :
    (ρ_ F).inv.toNatTrans.app X = eqToHom (by simp) := by simp

@[simp, push_cast]
/--
lemma `Hom.toNatIso_associator` / 引理 `Hom.toNatIso_associator`

English:
lemma Hom.toNatIso_associator
  given: {B C D E : Cat.{v, u}} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E)
  proof: rfl

@[simp, push_cast]

中文:
引理 态射.to自然数Iso_associator
  条件: {B C D E : Cat.{v, u}} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E)
  证明: rfl

@[simp, push_cast]
-/
lemma Hom.toNatIso_associator {B C D E : Cat.{v, u}} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) :
    Hom.toNatIso (α_ F G H) = Functor.associator F.toFunctor G.toFunctor H.toFunctor := rfl

@[simp, push_cast]
/--
lemma `associator_hom_toNatTrans` / 引理 `associator_hom_toNatTrans`

English:
lemma associator_hom_toNatTrans
  given: {B C D E : Cat.{v, u}} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E)
  proof: rfl

@[simp, push_cast]

中文:
引理 associator_hom_to自然数Trans
  条件: {B C D E : Cat.{v, u}} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E)
  证明: rfl

@[simp, push_cast]
-/
lemma associator_hom_toNatTrans {B C D E : Cat.{v, u}} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) :
    (α_ F G H).hom.toNatTrans = (Functor.associator F.toFunctor G.toFunctor H.toFunctor).hom := rfl

@[simp, push_cast]
/--
lemma `associator_inv_toNatTrans` / 引理 `associator_inv_toNatTrans`

English:
lemma associator_inv_toNatTrans
  given: {B C D E : Cat.{v, u}} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E)
  proof: rfl

中文:
引理 associator_inv_to自然数Trans
  条件: {B C D E : Cat.{v, u}} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E)
  证明: rfl
-/
lemma associator_inv_toNatTrans {B C D E : Cat.{v, u}} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) :
    (α_ F G H).inv.toNatTrans = (Functor.associator F.toFunctor G.toFunctor H.toFunctor).inv := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `associator_hom_app` / 引理 `associator_hom_app`

English:
lemma associator_hom_app
  given: {B C D E : Cat} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X : B)
  proof: by simp

中文:
引理 associator_hom_app
  条件: {B C D E : Cat} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X : B)
  证明: by simp
-/
lemma associator_hom_app {B C D E : Cat} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X : B) :
    (α_ F G H).hom.toNatTrans.app X = eqToHom (by simp) := by simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `associator_inv_app` / 引理 `associator_inv_app`

English:
lemma associator_inv_app
  given: {B C D E : Cat} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X : B)
  proof: by simp

中文:
引理 associator_inv_app
  条件: {B C D E : Cat} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X : B)
  证明: by simp
-/
lemma associator_inv_app {B C D E : Cat} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X : B) :
    (α_ F G H).inv.toNatTrans.app X = eqToHom (by simp) := by simp

/--
theorem `id_eq_id` / 定理 `id_eq_id`

English:
theorem id_eq_id
  given: (X : Cat.{u, v})
  statement: (𝟙 X : X ⟶ X).toFunctor = 𝟭 X
  proof: rfl

中文:
定理 id_eq_id
  条件: (X : Cat.{u, v})
  结论: (𝟙 X : X ⟶ X).toFunctor = 𝟭 X
  证明: rfl
-/
theorem id_eq_id (X : Cat.{u, v}) : (𝟙 X : X ⟶ X).toFunctor = 𝟭 X := rfl

/--
theorem `comp_eq_comp` / 定理 `comp_eq_comp`

English:
theorem comp_eq_comp
  given: {X Y Z : Cat} (F : X ⟶ Y) (G : Y ⟶ Z)
  proof: rfl

中文:
定理 comp_eq_comp
  条件: {X Y Z : Cat} (F : X ⟶ Y) (G : Y ⟶ Z)
  证明: rfl
-/
theorem comp_eq_comp {X Y Z : Cat} (F : X ⟶ Y) (G : Y ⟶ Z) :
    (F ≫ G).toFunctor = F.toFunctor ⋙ G.toFunctor := rfl

/--
theorem `of_α` / 定理 `of_α`

English:
theorem of_α
  given: (C) [Category* C]
  statement: (of C).α = C
  proof: rfl

中文:
定理 of_α
  条件: (C) [范畴* C]
  结论: (of C).α = C
  证明: rfl
-/
@[simp] theorem of_α (C) [Category* C] : (of C).α = C := rfl

/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (C : Cat.{v, u})
  statement: Cat.of C = C
  proof: rfl

中文:
定理 coe_of
  条件: (C : Cat.{v, u})
  结论: Cat.of C = C
  证明: rfl
-/
@[simp] theorem coe_of (C : Cat.{v, u}) : Cat.of C = C := rfl

/--
Definition of `objects` / `objects` 的定义

English:
definition objects
  signature: : Cat.{v, u} ⥤ Type u where
  body: C
  map F := ↾F.toFunctor.obj

中文:
定义 objects
  签名: : Cat.{v, u} ⥤ 类型u where
  定义体: C
  map F := ↾F.toFunctor.obj
-/
def objects : Cat.{v, u} ⥤ Type u where
  obj C := C
  map F := ↾F.toFunctor.obj

/-- See through the defeq `objects.obj X = X`. -/
instance (X : Cat.{v, u}) : Category (objects.obj X) := inferInstanceAs Category X

section

attribute [local simp] eqToHom_map

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `equivOfIso` / `equivOfIso` 的定义

English:
definition equivOfIso
  signature: {C D : Cat} (γ : C ≅ D)
  body: γ.hom.toFunctor
  inverse := γ.inv.toFunctor
unitIso := eqToIso congr($(γ.hom_inv_id).toFunctor).symm
counitIso := eqToIso congr($(γ.inv_hom_id).toFunctor)

中文:
定义 equivOfIso
  签名: {C D : Cat} (γ : C ≅ D)
  定义体: γ.hom.toFunctor
  inverse := γ.inv.toFunctor
unitIso := eqToIso congr($(γ.hom_inv_id).toFunctor).symm
counitIso := eqToIso congr($(γ.inv_hom_id).toFunctor)

Depends on / 依赖: hom.toFunctor, toFunctor
-/
def equivOfIso {C D : Cat} (γ : C ≅ D) : C ≌ D where
  functor := γ.hom.toFunctor
  inverse := γ.inv.toFunctor
unitIso := eqToIso congr($(γ.hom_inv_id).toFunctor).symm
counitIso := eqToIso congr($(γ.inv_hom_id).toFunctor)

/-- Under certain hypotheses, an equivalence of categories actually
defines an isomorphism in `Cat`. -/
@[simps]
/--
Definition of `isoOfEquiv` / `isoOfEquiv` 的定义

English:
definition isoOfEquiv
  signature: {C D : Cat.{v, u}} (e : C ≌ D)
  body: e.functor.toCatHom
  inv := e.inverse.toCatHom
  hom_inv_id := congrArg Functor.toCatHom
    (Functor.ext_of_iso e.unitIso (fun X => (h₁ X).symm) h₃).symm
  inv_hom_id := congrArg Functor.toCatHom (Functor.ext_of_iso e.counitIso h₂ h₄)

中文:
定义 isoOfEquiv
  签名: {C D : Cat.{v, u}} (e : C ≌ D)
  定义体: e.functor.toCatHom
  inv := e.inverse.toCatHom
  hom_inv_id := congrArg Functor.toCatHom
    (Functor.ext_of_iso e.unitIso (fun X => (h₁ X).symm) h₃).symm
  inv_hom_id := congrArg Functor.toCatHom (Functor.ext_of_iso e.counitIso h₂ h₄)

Depends on / 依赖: Functor, Functor.ext_of_iso, Functor.toCatHom, cat_disch, counitIso, e.counitIso, e.counitIso.hom.app, e.functor.toCatHom, e.inverse.toCatHom, e.unitIso, eqToHom, ext_of_iso, functor, hom_inv_id, inv_hom_id, inverse, toCatHom, unitIso
-/
def isoOfEquiv {C D : Cat.{v, u}} (e : C ≌ D)
    (h₁ : forall (X : C), e.inverse.obj (e.functor.obj X) = X)
    (h₂ : forall (Y : D), e.functor.obj (e.inverse.obj Y) = Y)
    (h₃ : forall (X : C), e.unitIso.hom.app X = eqToHom (h₁ X).symm := by cat_disch)
    (h₄ : forall (Y : D), e.counitIso.hom.app Y = eqToHom (h₂ Y) := by cat_disch) :
    C ≅ D where
  hom := e.functor.toCatHom
  inv := e.inverse.toCatHom
  hom_inv_id := congrArg Functor.toCatHom
    (Functor.ext_of_iso e.unitIso (fun X => (h₁ X).symm) h₃).symm
  inv_hom_id := congrArg Functor.toCatHom (Functor.ext_of_iso e.counitIso h₂ h₄)

end

end Cat

set_option backward.isDefEq.respectTransparency.types false in
/-- Embedding `Type` into `Cat` as discrete categories.

This ought to be modelled as a 2-functor!
-/
@[simps]
/--
Definition of `typeToCat` / `typeToCat` 的定义

English:
definition typeToCat
  signature: : Type u ⥤ Cat where
  body: Cat.of (Discrete X)
  map f := (Discrete.functor (Discrete.mk ∘ f)).toCatHom
  map_id X := by
    ext
    simp only [Cat.of_α, toCatHom_toFunctor, Cat.Hom.id_toFunctor]
    fapply Functor.ext
    · simp
    · intro X Y f
      cases f
      apply ULift.ext
      cat_disch
  map_comp f g := by
    ex

中文:
定义 typeToCat
  签名: : 类型u ⥤ Cat where
  定义体: Cat.of (Discrete X)
  map f := (Discrete.functor (Discrete.mk ∘ f)).toCatHom
  map_id X := by
    ext
    simp only [Cat.of_α, toCatHom_toFunctor, Cat.Hom.id_toFunctor]
    fapply Functor.ext
    · simp
    · intro X Y f
      cases f
      apply ULift.ext
      cat_disch
  map_comp f g := by
    ex

Depends on / 依赖: Cat.of, Discrete
-/
def typeToCat : Type u ⥤ Cat where
  obj X := Cat.of (Discrete X)
  map f := (Discrete.functor (Discrete.mk ∘ f)).toCatHom
  map_id X := by
    ext
    simp only [Cat.of_α, toCatHom_toFunctor, Cat.Hom.id_toFunctor]
    fapply Functor.ext
    · simp
    · intro X Y f
      cases f
      apply ULift.ext
      cat_disch
  map_comp f g := by
    ext
    simp only [Cat.of_α, toCatHom_toFunctor, Cat.Hom.comp_toFunctor]
    apply Functor.ext
    cat_disch

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor.Faithful typeToCat.{u}
  body: by
    ext x
    exact congrArg Discrete.as (Functor.congr_obj congr(($h).toFunctor) ⟨x⟩)

中文:
实例 :
  签名: 函子.忠实 typeToCat.{u}
  定义体: by
    ext x
    exact congrArg Discrete.as (Functor.congr_obj congr(($h).toFunctor) ⟨x⟩)

Depends on / 依赖: Category, Category.assoc, Discrete, Discrete.as, Functor, Functor.congr_obj, Functor.mapIso_inv, Functor.mapIso_symm, Functor.map_comp, Iso.symm_hom, Iso.trans_hom, congr_obj, coyonedaOpColimitIsoLimitCoyoneda, mapIso_inv, mapIso_symm, map_comp, symm_hom, toFunctor, trans_hom
-/
instance : Functor.Faithful typeToCat.{u} where
  map_injective {_X} {_Y} _f _g h := by
    ext x
    exact congrArg Discrete.as (Functor.congr_obj congr(($h).toFunctor) ⟨x⟩)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor.Full typeToCat.{u}
  body: ⟨↾(Discrete.as ∘ F.toFunctor.obj ∘ Discrete.mk), by
    ext
    refine Functor.ext (by cat_disch) ?_
    intro x y f
    apply ULift.ext
    cat_disch⟩

中文:
实例 :
  签名: 函子.满 typeToCat.{u}
  定义体: ⟨↾(Discrete.as ∘ F.toFunctor.obj ∘ Discrete.mk), by
    ext
    refine Functor.ext (by cat_disch) ?_
    intro x y f
    apply ULift.ext
    cat_disch⟩

Depends on / 依赖: Category, Category.assoc, Category.id_comp, Discrete, Discrete.as, Discrete.mk, F.toFunctor.obj, Functor, Functor.ext, Iso.inv_hom_id, ULift.ext, cat_disch, coyonedaOpColimitIsoLimitCoyoneda, id_comp, inv_hom_id, toFunctor
-/
instance : Functor.Full typeToCat.{u} where
  map_surjective F := ⟨↾(Discrete.as ∘ F.toFunctor.obj ∘ Discrete.mk), by
    ext
    refine Functor.ext (by cat_disch) ?_
    intro x y f
    apply ULift.ext
    cat_disch⟩

end CategoryTheory
