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
/-
**CategoryTheory.Cat** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：Cat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Category of categories.
-/
def Cat :=
  Bundled Category.{v, u}

namespace Cat

/-
**CategoryTheory.Cat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Cat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited Cat :=
  ⟨⟨Type u, CategoryTheory.types⟩⟩

-- TODO: maybe this coercion should be defined to be `objects.obj`?
/-
**CategoryTheory.Cat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Cat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort Cat (Type u) :=
  ⟨Bundled.α⟩
/-
**CategoryTheory.Cat.str** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：str (C : Cat.{v, u}) : Category.{v, u} C
参数：C : Cat.{v, u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance str (C : Cat.{v, u}) : Category.{v, u} C :=
  Bundled.str C

/-- Construct a bundled `Cat` from the underlying type and the typeclass. -/
/-
**CategoryTheory.Cat.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：of (C : Type u) [Category.{v} C] : Cat.{v, u}
参数：C : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `Cat` from the underlying type and the typeclass.
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
/-
**CategoryTheory.Cat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：CategoryTheory.Cat → CategoryTheory.Cat → Type (max u v)
参数：max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of 1-morphisms in the bicategory of categories `Cat`.
This is a structure around `Functor` to prevent defeq-abuse
-/
structure Hom (C D : Cat.{v, u}) where
  ofFunctor ::
  /-- The Functor underlying a 1-morphism in Cat -/
  toFunctor : C ⥤ D
/-
**CategoryTheory.Cat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Cat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Quiver (Cat.{v, u}) where
  Hom C D := Hom C D

/-- The 1-morphism in `Cat` corresponding to a functor. -/
@[simps, implicit_reducible]
/-
**CategoryTheory.Cat._root_.CategoryTheory.Functor.toCatHom** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Cat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 1-morphism in `Cat` corresponding to a functor.
-/
def _root_.CategoryTheory.Functor.toCatHom {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) : Cat.of C ⟶ Cat.of D where
  toFunctor := F

@[ext]
/-
**CategoryTheory.Cat.ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：ext {C D : Cat.{v, u}} {F G : C ⟶ D} (h : F.toFunctor = G.toFunctor) : F =
 G
参数：h : F.toFunctor = G.toFunctor。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma ext {C D : Cat.{v, u}} {F G : C ⟶ D} (h : F.toFunctor = G.toFunctor) : F = G :=
  congrArg (Functor.toCatHom) h

/--
The equivalence between the type of functors between two categories and
the type of 1-morphisms in Cat between the objects corresponding to those categories.
-/
@[simps]
/-
**CategoryTheory.Cat._root_.CategoryTheory.Functor.equivCatHom** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Cat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between the type of functors between two categories and
the type of 1-morphisms in Cat between the objects corresponding to those catego
ries.
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
/-
**CategoryTheory.Cat.Hom.equivFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Cat.Hom`。
形式化陈述：(C D : CategoryTheory.Cat) → (C ⟶ D) ≃ CategoryTheory.Functor ↑C ↑D
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The equivalence between the type of 1-morphisms in Cat between two objects
and the type of functors between the categories corresponding to those objects.
-/
def Hom.equivFunctor (C D : Cat.{v, u}) :
    (C ⟶ D) ≃ C ⥤ D := (equivCatHom _ _).symm

#adaptation_note /-- Removed `private`:
`ofNatTrans` was marked `private` in #31807,
but we have removed this when disabling `set_option backward.privateInPublic` as a global option. -/
/--
The type of 2-morphisms in the bicategory of categories `Cat`.
This is a wrapper around `NatTrans` to prevent defeq-abuse.
-/
/-
**CategoryTheory.Cat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：CategoryTheory.Cat → CategoryTheory.Cat → Type (max u v)
参数：max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of 2-morphisms in the bicategory of categories `Cat`.
This is a wrapper around `NatTrans` to prevent defeq-abuse.
-/
structure Hom₂ {C D : Cat.{v, u}} (F G : C ⟶ D) where
  ofNatTrans ::
  /-- The natural transformation underlying a 2-morphism in `Cat` -/
  toNatTrans : F.toFunctor ⟶ G.toFunctor

namespace Hom

/-
**CategoryTheory.Cat.Hom.instQuiver** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Ca
t.Hom`。
形式化陈述：instQuiver {C D : Cat.{v, u}} : Quiver (C ⟶ D) where Hom F G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instQuiver {C D : Cat.{v, u}} : Quiver (C ⟶ D) where
  Hom F G := Hom₂ F G

/-- The 2-morphism in `Cat` corresponding to a natural transformation between functors. -/
@[simps]
/-
**CategoryTheory.Cat.Hom._root_.CategoryTheory.NatTrans.toCatHom** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Cat.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 2-morphism in `Cat` corresponding to a natural transformation between functo
rs.
-/
def _root_.CategoryTheory.NatTrans.toCatHom₂ {C D : Type u} [Category.{v} C]
    [Category.{v} D] {F G : C ⥤ D} (η : F ⟶ G) : F.toCatHom ⟶ G.toCatHom where
  toNatTrans := η
/-
**CategoryTheory.Cat.Hom.instCategory** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Cat.Hom`。
形式化陈述：instCategory {X Y : Cat.{v, u}} : Category (X ⟶ Y) where id F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCategory {X Y : Cat.{v, u}} : Category (X ⟶ Y) where
  id F := NatTrans.toCatHom₂ (𝟙 F.toFunctor)
  comp η₁ η₂ := NatTrans.toCatHom₂ (η₁.toNatTrans ≫ η₂.toNatTrans)
  id_comp η := congrArg (NatTrans.toCatHom₂) (Category.id_comp η.toNatTrans)
  comp_id η := congrArg (NatTrans.toCatHom₂) (Category.comp_id η.toNatTrans)
  assoc η₁ η₂ η₃ :=
    congrArg (NatTrans.toCatHom₂) (Category.assoc η₁.toNatTrans η₂.toNatTrans η₃.toNatTrans)

@[simp, push_cast]
/-
**CategoryTheory.Cat.Hom._root_.CategoryTheory.NatTrans.toCatHom** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Cat.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CategoryTheory.NatTrans.toCatHom₂_id {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) :
    (𝟙 F : F ⟶ F).toCatHom₂ = 𝟙 F.toCatHom := rfl

@[simp, push_cast]
/-
**CategoryTheory.Cat.Hom._root_.CategoryTheory.NatTrans.toCatHom** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Cat.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CategoryTheory.NatTrans.toCatHom₂_comp {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G H : C ⥤ D} (η₁ : F ⟶ G) (η₂ : G ⟶ H) :
    (η₁ ≫ η₂).toCatHom₂ = η₁.toCatHom₂ ≫ η₂.toCatHom₂ := rfl

@[simp, push_cast]
/-
**CategoryTheory.Cat.Hom.toNatTrans_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Cat.Hom`。
形式化陈述：toNatTrans_id {C D : Cat.{v, u}} (F : C ⟶ D) : (𝟙 F : F ⟶ F).toNatTrans = 
𝟙 (F.toFunctor)
参数：F : C ⟶ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toNatTrans_id {C D : Cat.{v, u}} (F : C ⟶ D) :
  (𝟙 F : F ⟶ F).toNatTrans = 𝟙 (F.toFunctor) := rfl

@[simp, push_cast]
/-
**CategoryTheory.Cat.Hom.toNatTrans_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Cat.Hom`。
形式化陈述：toNatTrans_comp {C D : Cat.{v, u}} {F G H : C ⟶ D} (η₁ : F ⟶ G) (η₂ : G ⟶ 
H) : (η₁ ≫ η₂).toNatTrans = η₁.toNatTrans ≫ η₂.toNatTrans
参数：η₁ : F ⟶ G；η₂ : G ⟶ H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toNatTrans_comp {C D : Cat.{v, u}} {F G H : C ⟶ D} (η₁ : F ⟶ G) (η₂ : G ⟶ H) :
  (η₁ ≫ η₂).toNatTrans = η₁.toNatTrans ≫ η₂.toNatTrans := rfl

@[ext]
/-
**CategoryTheory.Cat.Hom._root_.CategoryTheory.Cat.Hom** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Cat.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CategoryTheory.Cat.Hom₂.ext {C D : Cat.{v, u}} {F G : C ⟶ D} {η₁ η₂ : F ⟶ G}
    (h : η₁.toNatTrans = η₂.toNatTrans) : η₁ = η₂ := congr($(h).toCatHom₂)

/-- The 2-iso in Cat corresponding to a natural isomorphism. -/
@[simps]
/-
**CategoryTheory.Cat.Hom.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cat.Hom
`。
形式化陈述：isoMk {C D : Type u} [Category.{v} C] [Category.{v} D] {F G : C ⥤ D} (e : 
F ≅ G) : F.toCatHom ≅ G.toCatHom where hom
参数：e : F ≅ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 2-iso in Cat corresponding to a natural isomorphism.
-/
def isoMk {C D : Type u} [Category.{v} C] [Category.{v} D] {F G : C ⥤ D} (e : F ≅ G) :
    F.toCatHom ≅ G.toCatHom where
  hom := e.hom.toCatHom₂
  inv := e.inv.toCatHom₂
  hom_inv_id := congrArg NatTrans.toCatHom₂ e.hom_inv_id
  inv_hom_id := congrArg NatTrans.toCatHom₂ e.inv_hom_id

/-- The natural isomorphism corresponding to a 2-iso in `Cat` -/
@[simps]
/-
**CategoryTheory.Cat.Hom.toNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cat.
Hom`。
形式化陈述：toNatIso {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) : F.toFunctor ≅ G.to
Functor where hom
参数：e : F ≅ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism corresponding to a 2-iso in `Cat`
-/
def toNatIso {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) : F.toFunctor ≅ G.toFunctor where
  hom := e.hom.toNatTrans
  inv := e.inv.toNatTrans
  hom_inv_id := congrArg Hom₂.toNatTrans e.hom_inv_id
  inv_hom_id := congrArg Hom₂.toNatTrans e.inv_hom_id

@[simp]
/-
**CategoryTheory.Cat.Hom.isoMk_toNatIso** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Cat.Hom`。
形式化陈述：isoMk_toNatIso {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) : isoMk (Hom.t
oNatIso e) = e
参数：e : F ≅ G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isoMk_toNatIso {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) :
    isoMk (Hom.toNatIso e) = e := rfl

@[simp]
/-
**CategoryTheory.Cat.Hom.toNatIso_isoMk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Cat.Hom`。
形式化陈述：toNatIso_isoMk {C D : Type u} [Category.{v} C] [Category.{v} D] {F G : C ⥤
 D} (e : F ≅ G) : Hom.toNatIso (isoMk e) = e
参数：e : F ≅ G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toNatIso_isoMk {C D : Type u} [Category.{v} C] [Category.{v} D] {F G : C ⥤ D} (e : F ≅ G) :
    Hom.toNatIso (isoMk e) = e := rfl
/-
**CategoryTheory.Cat.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Cat.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) :
    IsIso e.hom.toNatTrans :=
  (toNatIso e).isIso_hom
/-
**CategoryTheory.Cat.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Cat.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) :
    IsIso e.inv.toNatTrans :=
  (toNatIso e).isIso_inv

@[reassoc (attr := simp)]
/-
**CategoryTheory.Cat.Hom.hom_inv_id_toNatTrans** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Cat.Hom`。
形式化陈述：hom_inv_id_toNatTrans {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) : e.hom
.toNatTrans ≫ e.inv.toNatTrans = 𝟙 _
参数：e : F ≅ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
-/
lemma hom_inv_id_toNatTrans {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) :
    e.hom.toNatTrans ≫ e.inv.toNatTrans = 𝟙 _ :=
  (toNatIso e).hom_inv_id

@[reassoc (attr := simp)]
/-
**CategoryTheory.Cat.Hom.inv_hom_id_toNatTrans** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Cat.Hom`。
形式化陈述：inv_hom_id_toNatTrans {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) : e.inv
.toNatTrans ≫ e.hom.toNatTrans = 𝟙 _
参数：e : F ≅ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
-/
lemma inv_hom_id_toNatTrans {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) :
    e.inv.toNatTrans ≫ e.hom.toNatTrans = 𝟙 _ :=
  (toNatIso e).inv_hom_id

@[reassoc (attr := simp)]
/-
**CategoryTheory.Cat.Hom.hom_inv_id_toNatTrans_app** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Cat.Hom`。
形式化陈述：hom_inv_id_toNatTrans_app {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) (A 
: X) : e.hom.toNatTrans.app A ≫ e.inv.toNatTrans.app A = 𝟙 _
参数：e : F ≅ G；A : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
-/
lemma hom_inv_id_toNatTrans_app {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) (A : X) :
    e.hom.toNatTrans.app A ≫ e.inv.toNatTrans.app A = 𝟙 _ :=
  (toNatIso e).hom_inv_id_app A

@[reassoc (attr := simp)]
/-
**CategoryTheory.Cat.Hom.inv_hom_id_toNatTrans_app** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Cat.Hom`。
形式化陈述：inv_hom_id_toNatTrans_app {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) (A 
: X) : e.inv.toNatTrans.app A ≫ e.hom.toNatTrans.app A = 𝟙 _
参数：e : F ≅ G；A : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
-/
lemma inv_hom_id_toNatTrans_app {X Y : Cat.{v, u}} {F G : X ⟶ Y} (e : F ≅ G) (A : X) :
    e.inv.toNatTrans.app A ≫ e.hom.toNatTrans.app A = 𝟙 _ :=
  (toNatIso e).inv_hom_id_app A

end Hom

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Bicategory structure on `Cat` -/
/-
**CategoryTheory.Cat.bicategory** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：bicategory : Bicategory.{max v u, max v u} Cat.{v, u} where id C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bicategory structure on `Cat`
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

/-- `Cat` is a strict bicategory. -/
/-
**CategoryTheory.Cat.bicategory.strict** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Cat.bicategory`。
形式化陈述：CategoryTheory.Bicategory.Strict CategoryTheory.Cat
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`Cat` is a strict bicategory.
-/
instance bicategory.strict : Bicategory.Strict Cat.{v, u} where
  id_comp {C} {D} F := by cases F; rfl
  comp_id {C} {D} F := by cases F; rfl
  assoc := by intros; rfl

/-- Category structure on `Cat` -/
/-
**CategoryTheory.Cat.category** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：category : LargeCategory.{max v u} Cat.{v, u}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Cat.bicategory.strict`：CategoryTheory.Bicategory.Strict C
ategoryTheory.Cat

--- 原说明 ---
Category structure on `Cat`
-/
instance category : LargeCategory.{max v u} Cat.{v, u} :=
  StrictBicategory.category Cat.{v, u}

@[simp, push_cast]
/-
**CategoryTheory.Cat.Hom.id_toFunctor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Cat.Hom`。
形式化陈述：∀ {C : CategoryTheory.Cat}, (CategoryTheory.CategoryStruct.id C).toFunctor
 = CategoryTheory.Functor.id ↑C
参数：CategoryTheory.CategoryStruct.id C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.id_toFunctor {C : Cat.{v, u}} : (𝟙 C : C ⟶ C).toFunctor = 𝟭 C := rfl

@[simp]
/-
**CategoryTheory.Cat.Hom.id_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Cat.Ho
m`。
形式化陈述：∀ {C : CategoryTheory.Cat} (X : ↑C), (CategoryTheory.CategoryStruct.id C).
toFunctor.obj X = X
参数：X : ↑C；CategoryTheory.CategoryStruct.id C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Hom.id_obj {C : Cat.{v, u}} (X : C) : (𝟙 C : C ⟶ C).toFunctor.obj X = X := by
  simp

@[simp]
/-
**CategoryTheory.Cat.Hom.id_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Cat.Ho
m`。
形式化陈述：∀ {C : CategoryTheory.Cat} {X Y : ↑C} (f : X ⟶ Y), (CategoryTheory.Categor
yStruct.id C).toFunctor.map f = f
参数：f : X ⟶ Y；CategoryTheory.CategoryStruct.id C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Hom.id_map {C : Cat.{v, u}} {X Y : C} (f : X ⟶ Y) : (𝟙 C : C ⟶ C).toFunctor.map f = f := by
  simp

@[simp, push_cast]
/-
**CategoryTheory.Cat.Hom.comp_toFunctor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Cat.Hom`。
形式化陈述：∀ {C D E : CategoryTheory.Cat} (F : C ⟶ D) (G : D ⟶ E),   (CategoryTheory.
CategoryStruct.comp F G).toFunctor = F.toFunctor.comp G.toFunctor
参数：F : C ⟶ D；G : D ⟶ E；CategoryTheory.CategoryStruct.comp F G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.comp_toFunctor {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) :
  (F ≫ G).toFunctor = F.toFunctor ⋙ G.toFunctor := rfl
/-
**CategoryTheory.Cat.Hom.comp_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Cat.
Hom`。
形式化陈述：∀ {C D E : CategoryTheory.Cat} (F : C ⟶ D) (G : D ⟶ E) (X : ↑C),   (Catego
ryTheory.CategoryStruct.comp F G).toFunctor.obj X = G.toFunctor.obj (F.toFunctor
.obj X)
参数：F : C ⟶ D；G : D ⟶ E；X : ↑C；CategoryTheory.CategoryStruct.comp F G；F.toFunctor
.obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Hom.comp_obj {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) (X : C) :
    (F ≫ G).toFunctor.obj X = G.toFunctor.obj (F.toFunctor.obj X) := by
  simp

@[simp]
/-
**CategoryTheory.Cat.Hom.comp_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Cat.
Hom`。
形式化陈述：∀ {C D E : CategoryTheory.Cat} (F : C ⟶ D) (G : D ⟶ E) {X Y : ↑C} (f : X ⟶
 Y),   (CategoryTheory.CategoryStruct.comp F G).toFunctor.map f = G.toFunctor.ma
p (F.toFunctor.map f)
参数：F : C ⟶ D；G : D ⟶ E；f : X ⟶ Y；CategoryTheory.CategoryStruct.comp F G；F.toFunc
tor.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Hom.comp_map {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) {X Y : C} (f : X ⟶ Y) :
    (F ≫ G).toFunctor.map f = G.toFunctor.map (F.toFunctor.map f) := by
  simp

@[simp]
/-
**CategoryTheory.Cat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：CategoryTheory.Cat → CategoryTheory.Cat → Type (max u v)
参数：max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Hom₂.id_app {C D : Cat.{v, u}} (F : C ⟶ D) (X : C) :
    (𝟙 F : F ⟶ F).toNatTrans.app X = 𝟙 (F.toFunctor.obj X) := by
  simp

@[simp, reassoc]
/-
**CategoryTheory.Cat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：CategoryTheory.Cat → CategoryTheory.Cat → Type (max u v)
参数：max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Hom₂.comp_app {C D : Cat.{v, u}} {F G H : C ⟶ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) :
    (α ≫ β).toNatTrans.app X = α.toNatTrans.app X ≫ β.toNatTrans.app X := rfl

@[simp]
/-
**CategoryTheory.Cat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：CategoryTheory.Cat → CategoryTheory.Cat → Type (max u v)
参数：max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Hom₂.eqToHom_toNatTrans {C D : Cat.{v, u}} {F G : C ⟶ D} (h : F = G) :
  (eqToHom h).toNatTrans = eqToHom congr(($h).toFunctor) := by cases h; simp
/-
**CategoryTheory.Cat.eqToHom_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：eqToHom_app {C D : Cat.{v, u}} (F G : C ⟶ D) (h : F = G) (X : C) : (eqToHo
m h).toNatTrans.app X = eqToHom congr(($h).toFunctor.obj X)
参数：F G : C ⟶ D；h : F = G；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Cat.Hom₂.eqToHom_toNatTrans`：∀ {C D : CategoryTheory.Cat}
 {F G : C ⟶ D} (h : F = G), (CategoryTheory.eqToHom h).toNatTrans = CategoryTheo
ry.eqToHom ⋯
· 使用定理 `CategoryTheory.eqToHom_app`：eqToHom_app {F G : C ⥤ D} (h : F = G) (X : C
) : (eqToHom h : F ⟶ G).app X = eqToHom (Functor.congr_obj h X)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eqToHom_app {C D : Cat.{v, u}} (F G : C ⟶ D) (h : F = G) (X : C) :
    (eqToHom h).toNatTrans.app X = eqToHom congr(($h).toFunctor.obj X) := by
  simp

@[simp, push_cast]
/-
**CategoryTheory.Cat.whiskerLeft_toNatTrans** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Cat`。
形式化陈述：whiskerLeft_toNatTrans {C D E : Cat.{v, u}} (F : C ⟶ D) {G H : D ⟶ E} (η :
 G ⟶ H) : (F ◁ η).toNatTrans = F.toFunctor.whiskerLeft η.toNatTrans
参数：F : C ⟶ D；η : G ⟶ H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerLeft_toNatTrans {C D E : Cat.{v, u}} (F : C ⟶ D) {G H : D ⟶ E} (η : G ⟶ H) :
  (F ◁ η).toNatTrans = F.toFunctor.whiskerLeft η.toNatTrans := rfl
/-
**CategoryTheory.Cat.whiskerLeft_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.C
at`。
形式化陈述：whiskerLeft_app {C D E : Cat.{v, u}} (F : C ⟶ D) {G H : D ⟶ E} (η : G ⟶ H)
 (X : C) : (F ◁ η).toNatTrans.app X = η.toNatTrans.app (F.toFunctor.obj X)
参数：F : C ⟶ D；η : G ⟶ H；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerLeft_app {C D E : Cat.{v, u}} (F : C ⟶ D) {G H : D ⟶ E} (η : G ⟶ H) (X : C) :
    (F ◁ η).toNatTrans.app X = η.toNatTrans.app (F.toFunctor.obj X) := by simp

@[simp, push_cast]
/-
**CategoryTheory.Cat.whiskerRight_toNatTrans** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Cat`。
形式化陈述：whiskerRight_toNatTrans {C D E : Cat.{v, u}} {F G : C ⟶ D} (H : D ⟶ E) (η 
: F ⟶ G) : (η ▷ H).toNatTrans = Functor.whiskerRight η.toNatTrans H.toFunctor
参数：H : D ⟶ E；η : F ⟶ G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerRight_toNatTrans {C D E : Cat.{v, u}} {F G : C ⟶ D} (H : D ⟶ E) (η : F ⟶ G) :
    (η ▷ H).toNatTrans = Functor.whiskerRight η.toNatTrans H.toFunctor := rfl
/-
**CategoryTheory.Cat.whiskerRight_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Cat`。
形式化陈述：whiskerRight_app {C D E : Cat.{v, u}} {F G : C ⟶ D} (H : D ⟶ E) (η : F ⟶ G
) (X : C) : (η ▷ H).toNatTrans.app X = H.toFunctor.map (η.toNatTrans.app X)
参数：H : D ⟶ E；η : F ⟶ G；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerRight_app {C D E : Cat.{v, u}} {F G : C ⟶ D} (H : D ⟶ E) (η : F ⟶ G) (X : C) :
    (η ▷ H).toNatTrans.app X = H.toFunctor.map (η.toNatTrans.app X) := by simp

@[simp, push_cast]
/-
**CategoryTheory.Cat.Hom.toNatIso_leftUnitor** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Cat.Hom`。
形式化陈述：∀ {B C : CategoryTheory.Cat} (F : B ⟶ C),   CategoryTheory.Cat.Hom.toNatIs
o (CategoryTheory.Bicategory.leftUnitor F) = F.toFunctor.leftUnitor
参数：F : B ⟶ C；CategoryTheory.Bicategory.leftUnitor F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.toNatIso_leftUnitor {B C : Cat.{v, u}} (F : B ⟶ C) :
    Hom.toNatIso (λ_ F) = F.toFunctor.leftUnitor := rfl

@[simp, push_cast]
/-
**CategoryTheory.Cat.leftUnitor_hom_toNatTrans** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Cat`。
形式化陈述：leftUnitor_hom_toNatTrans {B C : Cat.{v, u}} (F : B ⟶ C) : (fun_ F).hom.to
NatTrans = (F.toFunctor.leftUnitor).hom
参数：F : B ⟶ C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma leftUnitor_hom_toNatTrans {B C : Cat.{v, u}} (F : B ⟶ C) :
    (λ_ F).hom.toNatTrans = (F.toFunctor.leftUnitor).hom := rfl

@[simp, push_cast]
/-
**CategoryTheory.Cat.leftUnitor_inv_toNatTrans** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Cat`。
形式化陈述：leftUnitor_inv_toNatTrans {B C : Cat.{v, u}} (F : B ⟶ C) : (fun_ F).inv.to
NatTrans = (F.toFunctor.leftUnitor).inv
参数：F : B ⟶ C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma leftUnitor_inv_toNatTrans {B C : Cat.{v, u}} (F : B ⟶ C) :
    (λ_ F).inv.toNatTrans = (F.toFunctor.leftUnitor).inv := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Cat.leftUnitor_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Cat`。
形式化陈述：leftUnitor_hom_app {B C : Cat} (F : B ⟶ C) (X : B) : (fun_ F).hom.toNatTra
ns.app X = eqToHom (by simp)
参数：F : B ⟶ C；X : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftUnitor_hom_app {B C : Cat} (F : B ⟶ C) (X : B) :
    (λ_ F).hom.toNatTrans.app X = eqToHom (by simp) := by simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Cat.leftUnitor_inv_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Cat`。
形式化陈述：leftUnitor_inv_app {B C : Cat} (F : B ⟶ C) (X : B) : (fun_ F).inv.toNatTra
ns.app X = eqToHom (by simp)
参数：F : B ⟶ C；X : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftUnitor_inv_app {B C : Cat} (F : B ⟶ C) (X : B) :
    (λ_ F).inv.toNatTrans.app X = eqToHom (by simp) := by simp

@[simp, push_cast]
/-
**CategoryTheory.Cat.Hom.toNatIso_rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Cat.Hom`。
形式化陈述：∀ {B C : CategoryTheory.Cat} (F : B ⟶ C),   CategoryTheory.Cat.Hom.toNatIs
o (CategoryTheory.Bicategory.rightUnitor F) =     CategoryTheory.eqToIso ⋯ ≪≫ F.
toFunctor.rightUnitor ≪≫ CategoryTheory.eqToIso ⋯
参数：F : B ⟶ C；CategoryTheory.Bicategory.rightUnitor F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Iso.trans_refl`：trans_refl (α : X ≅ Y) : α ≪≫ Iso.refl Y 
= α
· 使用定理 `CategoryTheory.Iso.refl_trans`：refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α 
= α
-/
lemma Hom.toNatIso_rightUnitor {B C : Cat.{v, u}} (F : B ⟶ C) :
    Hom.toNatIso (ρ_ F) = eqToIso rfl ≪≫ F.toFunctor.rightUnitor ≪≫ eqToIso rfl := by simp; rfl

@[simp, push_cast]
/-
**CategoryTheory.Cat.rightUnitor_hom_toNatTrans** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Cat`。
形式化陈述：rightUnitor_hom_toNatTrans {B C : Cat.{v, u}} (F : B ⟶ C) : (ρ_ F).hom.toN
atTrans = (F.toFunctor.rightUnitor).hom
参数：F : B ⟶ C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rightUnitor_hom_toNatTrans {B C : Cat.{v, u}} (F : B ⟶ C) :
    (ρ_ F).hom.toNatTrans = (F.toFunctor.rightUnitor).hom := rfl

@[simp, push_cast]
/-
**CategoryTheory.Cat.rightUnitor_inv_toNatTrans** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Cat`。
形式化陈述：rightUnitor_inv_toNatTrans {B C : Cat.{v, u}} (F : B ⟶ C) : (ρ_ F).inv.toN
atTrans = (F.toFunctor.rightUnitor).inv
参数：F : B ⟶ C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rightUnitor_inv_toNatTrans {B C : Cat.{v, u}} (F : B ⟶ C) :
    (ρ_ F).inv.toNatTrans = (F.toFunctor.rightUnitor).inv := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Cat.rightUnitor_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Cat`。
形式化陈述：rightUnitor_hom_app {B C : Cat.{v, u}} (F : B ⟶ C) (X : B) : (ρ_ F).hom.to
NatTrans.app X = eqToHom (by simp)
参数：F : B ⟶ C；X : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightUnitor_hom_app {B C : Cat.{v, u}} (F : B ⟶ C) (X : B) :
    (ρ_ F).hom.toNatTrans.app X = eqToHom (by simp) := by simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Cat.rightUnitor_inv_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Cat`。
形式化陈述：rightUnitor_inv_app {B C : Cat.{v, u}} (F : B ⟶ C) (X : B) : (ρ_ F).inv.to
NatTrans.app X = eqToHom (by simp)
参数：F : B ⟶ C；X : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightUnitor_inv_app {B C : Cat.{v, u}} (F : B ⟶ C) (X : B) :
    (ρ_ F).inv.toNatTrans.app X = eqToHom (by simp) := by simp

@[simp, push_cast]
/-
**CategoryTheory.Cat.Hom.toNatIso_associator** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Cat.Hom`。
形式化陈述：∀ {B C D E : CategoryTheory.Cat} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E),   Ca
tegoryTheory.Cat.Hom.toNatIso (CategoryTheory.Bicategory.associator F G H) =    
 F.toFunctor.associator G.toFunctor H.toFunctor
参数：F : B ⟶ C；G : C ⟶ D；H : D ⟶ E；CategoryTheory.Bicategory.associator F G H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.toNatIso_associator {B C D E : Cat.{v, u}} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) :
    Hom.toNatIso (α_ F G H) = Functor.associator F.toFunctor G.toFunctor H.toFunctor := rfl

@[simp, push_cast]
/-
**CategoryTheory.Cat.associator_hom_toNatTrans** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Cat`。
形式化陈述：associator_hom_toNatTrans {B C D E : Cat.{v, u}} (F : B ⟶ C) (G : C ⟶ D) (
H : D ⟶ E) : (α_ F G H).hom.toNatTrans = (Functor.associator F.toFunctor G.toFun
ctor H.toFunctor).hom
参数：F : B ⟶ C；G : C ⟶ D；H : D ⟶ E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma associator_hom_toNatTrans {B C D E : Cat.{v, u}} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) :
    (α_ F G H).hom.toNatTrans = (Functor.associator F.toFunctor G.toFunctor H.toFunctor).hom := rfl

@[simp, push_cast]
/-
**CategoryTheory.Cat.associator_inv_toNatTrans** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Cat`。
形式化陈述：associator_inv_toNatTrans {B C D E : Cat.{v, u}} (F : B ⟶ C) (G : C ⟶ D) (
H : D ⟶ E) : (α_ F G H).inv.toNatTrans = (Functor.associator F.toFunctor G.toFun
ctor H.toFunctor).inv
参数：F : B ⟶ C；G : C ⟶ D；H : D ⟶ E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma associator_inv_toNatTrans {B C D E : Cat.{v, u}} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) :
    (α_ F G H).inv.toNatTrans = (Functor.associator F.toFunctor G.toFunctor H.toFunctor).inv := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Cat.associator_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Cat`。
形式化陈述：associator_hom_app {B C D E : Cat} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X 
: B) : (α_ F G H).hom.toNatTrans.app X = eqToHom (by simp)
参数：F : B ⟶ C；G : C ⟶ D；H : D ⟶ E；X : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma associator_hom_app {B C D E : Cat} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X : B) :
    (α_ F G H).hom.toNatTrans.app X = eqToHom (by simp) := by simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Cat.associator_inv_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Cat`。
形式化陈述：associator_inv_app {B C D E : Cat} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X 
: B) : (α_ F G H).inv.toNatTrans.app X = eqToHom (by simp)
参数：F : B ⟶ C；G : C ⟶ D；H : D ⟶ E；X : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma associator_inv_app {B C D E : Cat} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E) (X : B) :
    (α_ F G H).inv.toNatTrans.app X = eqToHom (by simp) := by simp

/-- The identity in the category of categories equals the identity functor. -/
/-
**CategoryTheory.Cat.id_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：id_eq_id (X : Cat.{u, v}) : (𝟙 X : X ⟶ X).toFunctor = 𝟭 X
参数：X : Cat.{u, v}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity in the category of categories equals the identity functor.
-/
theorem id_eq_id (X : Cat.{u, v}) : (𝟙 X : X ⟶ X).toFunctor = 𝟭 X := rfl

/-- Composition in the category of categories equals functor composition. -/
/-
**CategoryTheory.Cat.comp_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Cat`
。
形式化陈述：comp_eq_comp {X Y Z : Cat} (F : X ⟶ Y) (G : Y ⟶ Z) : (F ≫ G).toFunctor = F
.toFunctor ⋙ G.toFunctor
参数：F : X ⟶ Y；G : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition in the category of categories equals functor composition.
-/
theorem comp_eq_comp {X Y Z : Cat} (F : X ⟶ Y) (G : Y ⟶ Z) :
    (F ≫ G).toFunctor = F.toFunctor ⋙ G.toFunctor := rfl
/-
**CategoryTheory.Cat.of_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Cat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem of_α (C) [Category* C] : (of C).α = C := rfl
/-
**CategoryTheory.Cat.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：∀ (C : CategoryTheory.Cat), CategoryTheory.Cat.of ↑C = C
参数：C : CategoryTheory.Cat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_of (C : Cat.{v, u}) : Cat.of C = C := rfl

/-- Functor that gets the set of objects of a category. It is not
called `forget`, because it is not a faithful functor. -/
/-
**CategoryTheory.Cat.objects** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：objects : Cat.{v, u} ⥤ Type u where obj C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functor that gets the set of objects of a category. It is not
called `forget`, because it is not a faithful functor.
-/
def objects : Cat.{v, u} ⥤ Type u where
  obj C := C
  map F := ↾F.toFunctor.obj

/-- See through the defeq `objects.obj X = X`. -/
/-
**CategoryTheory.Cat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Cat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See through the defeq `objects.obj X = X`.
-/
instance (X : Cat.{v, u}) : Category (objects.obj X) := inferInstanceAs <| Category X

section

attribute [local simp] eqToHom_map

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Any isomorphism in `Cat` induces an equivalence of the underlying categories. -/
/-
**CategoryTheory.Cat.equivOfIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：equivOfIso {C D : Cat} (γ : C ≅ D) : C ≌ D where functor
参数：γ : C ≅ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any isomorphism in `Cat` induces an equivalence of the underlying categories.
-/
def equivOfIso {C D : Cat} (γ : C ≅ D) : C ≌ D where
  functor := γ.hom.toFunctor
  inverse := γ.inv.toFunctor
  unitIso := eqToIso <| congr($(γ.hom_inv_id).toFunctor).symm
  counitIso := eqToIso <| congr($(γ.inv_hom_id).toFunctor)

/-- Under certain hypotheses, an equivalence of categories actually
defines an isomorphism in `Cat`. -/
@[simps]
/-
**CategoryTheory.Cat.isoOfEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cat`。
形式化陈述：isoOfEquiv {C D : Cat.{v, u}} (e : C ≌ D) (h₁ : forall (X : C), e.inverse.
obj (e.functor.obj X) = X) (h₂ : forall (Y : D), e.functor.obj (e.inverse.obj Y)
 = Y) (h₃ : forall (X : C), e.unitIso.hom.app X = eqToHom (h₁ X).symm
参数：e : C ≌ D；h₁ : forall (X : C), e.inverse.obj (e.functor.obj X) = X；h₂ : foral
l (Y : D), e.functor.obj (e.inverse.obj Y) = Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Under certain hypotheses, an equivalence of categories actually
defines an isomorphism in `Cat`.
-/
def isoOfEquiv {C D : Cat.{v, u}} (e : C ≌ D)
    (h₁ : ∀ (X : C), e.inverse.obj (e.functor.obj X) = X)
    (h₂ : ∀ (Y : D), e.functor.obj (e.inverse.obj Y) = Y)
    (h₃ : ∀ (X : C), e.unitIso.hom.app X = eqToHom (h₁ X).symm := by cat_disch)
    (h₄ : ∀ (Y : D), e.counitIso.hom.app Y = eqToHom (h₂ Y) := by cat_disch) :
    C ≅ D where
  hom := e.functor.toCatHom
  inv := e.inverse.toCatHom
  hom_inv_id := congrArg Functor.toCatHom
    (Functor.ext_of_iso e.unitIso (fun X ↦ (h₁ X).symm) h₃).symm
  inv_hom_id := congrArg Functor.toCatHom (Functor.ext_of_iso e.counitIso h₂ h₄)

end

end Cat

set_option backward.isDefEq.respectTransparency.types false in
/-- Embedding `Type` into `Cat` as discrete categories.

This ought to be modelled as a 2-functor!
-/
@[simps]
/-
**CategoryTheory.typeToCat** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：typeToCat : Type u ⥤ Cat where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embedding `Type` into `Cat` as discrete categories.

This ought to be modelled as a 2-functor!
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
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Functor.Faithful typeToCat.{u} where
  map_injective {_X} {_Y} _f _g h := by
    ext x
    exact congrArg Discrete.as (Functor.congr_obj congr(($h).toFunctor) ⟨x⟩)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Functor.Full typeToCat.{u} where
  map_surjective F := ⟨↾(Discrete.as ∘ F.toFunctor.obj ∘ Discrete.mk), by
    ext
    refine Functor.ext (by cat_disch) ?_
    intro x y f
    apply ULift.ext
    cat_disch⟩

end CategoryTheory

