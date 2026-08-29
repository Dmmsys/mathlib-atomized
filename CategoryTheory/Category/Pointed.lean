/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The category of pointed types

This defines `Pointed`, the category of pointed types.

## TODO

* Monoidal structure
* Upgrade `typeToPointed` to an equivalence
-/

@[expose] public section


open CategoryTheory

universe u

/--
Definition of `Pointed` / `Pointed` 的定义

English:
structure Pointed
  parameters: : Type (u + 1) where
  axioms and operations (2):
    - X : Type u
    - point : X

中文:
结构 Pointed
  参数: : 类型 (u + 1) where
  公理与运算 (2 个):
    - X : 类型u
    - point : X
-/
structure Pointed : Type (u + 1) where
  /-- the underlying type -/
  protected X : Type u
  /-- the distinguished element -/
  point : X

namespace Pointed

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort Pointed Type*
  body: ⟨Pointed.X⟩

中文:
实例 :
  签名: CoeSort Pointed 类型
  定义体: ⟨Pointed.X⟩

Depends on / 依赖: Pointed, Pointed.X
-/
instance : CoeSort Pointed Type* :=
  ⟨Pointed.X⟩

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: {X : Type*} (point : X)
  body: ⟨X, point⟩

中文:
缩写 of
  签名: {X : 类型} (point : X)
  定义体: ⟨X, point⟩
-/
abbrev of {X : Type*} (point : X) : Pointed :=
  ⟨X, point⟩

/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: {X : Type*} (point : X)
  statement: ↥(of point) = X
  proof: rfl

alias _root_.Prod.Pointed := of

中文:
定理 coe_of
  条件: {X : 类型} (point : X)
  结论: ↥(of point) = X
  证明: rfl

alias _root_.Prod.Pointed := of
-/
theorem coe_of {X : Type*} (point : X) : ↥(of point) = X :=
  rfl

alias _root_.Prod.Pointed := of

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited Pointed
  body: ⟨of ((), ())⟩

中文:
实例 :
  签名: 可居 Pointed
  定义体: ⟨of ((), ())⟩
-/
instance : Inhabited Pointed :=
  ⟨of ((), ())⟩

/-- Morphisms in `Pointed`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : Pointed.{u})
  axioms and operations (2):
    - toFun : X -> Y
    - map_point : toFun X.point = Y.point

中文:
结构 态射
  参数: (X Y : Pointed.{u})
  公理与运算 (2 个):
    - toFun : X -> Y
    - map_point : toFun X.point = Y.point
-/
protected structure Hom (X Y : Pointed.{u}) : Type u where
  /-- the underlying map -/
  toFun : X -> Y
  /-- compatibility with the distinguished points -/
  map_point : toFun X.point = Y.point

namespace Hom

/-- The identity morphism of `X : Pointed`. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (X : Pointed)
  body: ⟨_root_.id, rfl⟩

中文:
定义 id
  签名: (X : Pointed)
  定义体: ⟨_root_.id, rfl⟩

Depends on / 依赖: _root_, _root_.id
-/
def id (X : Pointed) : Pointed.Hom X X :=
  ⟨_root_.id, rfl⟩

instance (X : Pointed) : Inhabited (Pointed.Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms of `Pointed`. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {X Y Z : Pointed.{u}} (f : Pointed.Hom X Y) (g : Pointed.Hom Y Z)
  body: ⟨g.toFun ∘ f.toFun, by rw [Function.comp_apply, f.map_point, g.map_point]⟩

中文:
定义 comp
  签名: {X Y Z : Pointed.{u}} (f : Pointed.态射 X Y) (g : Pointed.态射 Y Z)
  定义体: ⟨g.toFun ∘ f.toFun, by rw [Function.comp_apply, f.map_point, g.map_point]⟩

Depends on / 依赖: Function, Function.comp_apply, comp_apply, f.map_point, f.toFun, g.map_point, g.toFun, map_point
-/
def comp {X Y Z : Pointed.{u}} (f : Pointed.Hom X Y) (g : Pointed.Hom Y Z) : Pointed.Hom X Z :=
  ⟨g.toFun ∘ f.toFun, by rw [Function.comp_apply, f.map_point, g.map_point]⟩

end Hom

/--
Instance `largeCategory` / 实例 `largeCategory`

English:
instance largeCategory
  signature: : LargeCategory Pointed where
  body: Pointed.Hom
  id := Hom.id
  comp := @Hom.comp

中文:
实例 largeCategory
  签名: : 大范畴 Pointed where
  定义体: Pointed.Hom
  id := Hom.id
  comp := @Hom.comp

Depends on / 依赖: Pointed, Pointed.Hom
-/
instance largeCategory : LargeCategory Pointed where
  Hom := Pointed.Hom
  id := Hom.id
  comp := @Hom.comp

/--
lemma `Hom.id_toFun'` / 引理 `Hom.id_toFun'`

English:
lemma Hom.id_toFun'
  given: (X : Pointed.{u})
  statement: (𝟙 X : X ⟶ X).toFun = _root_.id
  proof: rfl

中文:
引理 态射.id_toFun'
  条件: (X : Pointed.{u})
  结论: (𝟙 X : X ⟶ X).toFun = _root_.id
  证明: rfl
-/
@[simp] lemma Hom.id_toFun' (X : Pointed.{u}) : (𝟙 X : X ⟶ X).toFun = _root_.id := rfl

/--
lemma `Hom.comp_toFun'` / 引理 `Hom.comp_toFun'`

English:
lemma Hom.comp_toFun'
  given: {X Y Z : Pointed.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 态射.comp_toFun'
  条件: {X Y Z : Pointed.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
@[simp] lemma Hom.comp_toFun' {X Y Z : Pointed.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl

instance (X Y : Pointed) : FunLike { f : X -> Y // f X.point = Y.point } X Y where
  coe f := f
  coe_injective _ _ := Subtype.ext

/--
Instance `hasForget` / 实例 `hasForget`

English:
instance hasForget
  signature: : ConcreteCategory Pointed fun X Y => { f : X -> Y // f X.point = Y.point } where
  body: ⟨f.1, f.2⟩
  ofHom f := ⟨f.1, f.2⟩

中文:
实例 hasForget
  签名: : 余ncrete范畴 Pointed fun X Y => { f : X -> Y // f X.point = Y.point } where
  定义体: ⟨f.1, f.2⟩
  ofHom f := ⟨f.1, f.2⟩
-/
instance hasForget : ConcreteCategory Pointed fun X Y => { f : X -> Y // f X.point = Y.point } where
  hom f := ⟨f.1, f.2⟩
  ofHom f := ⟨f.1, f.2⟩

/-- Constructs an isomorphism between pointed types from an equivalence that preserves the point
between them. -/
@[simps]
/--
Definition of `Iso.mk` / `Iso.mk` 的定义

English:
definition Iso.mk
  signature: {α β : Pointed} (e : α ≃ β) (he : e α.point = β.point)
  body: ⟨e, he⟩
  inv := ⟨e.symm, e.symm_apply_eq.2 he.symm⟩
  hom_inv_id := Pointed.Hom.ext e.symm_comp_self
  inv_hom_id := Pointed.Hom.ext e.self_comp_symm

中文:
定义 同构.mk
  签名: {α β : Pointed} (e : α ≃ β) (he : e α.point = β.point)
  定义体: ⟨e, he⟩
  inv := ⟨e.symm, e.symm_apply_eq.2 he.symm⟩
  hom_inv_id := Pointed.Hom.ext e.symm_comp_self
  inv_hom_id := Pointed.Hom.ext e.self_comp_symm
-/
def Iso.mk {α β : Pointed} (e : α ≃ β) (he : e α.point = β.point) : α ≅ β where
  hom := ⟨e, he⟩
  inv := ⟨e.symm, e.symm_apply_eq.2 he.symm⟩
  hom_inv_id := Pointed.Hom.ext e.symm_comp_self
  inv_hom_id := Pointed.Hom.ext e.self_comp_symm

end Pointed

/-- `Option` as a functor from types to pointed types. This is the free functor. -/
@[simps]
/--
Definition of `typeToPointed` / `typeToPointed` 的定义

English:
definition typeToPointed
  signature: : Type u ⥤ Pointed.{u} where
  body: ⟨Option X, none⟩
  map f := ⟨Option.map f, rfl⟩
  map_id _ := Pointed.Hom.ext Option.map_id
map_comp _ _ := Pointed.Hom.ext by simp; rfl

中文:
定义 typeToPointed
  签名: : 类型u ⥤ Pointed.{u} where
  定义体: ⟨Option X, none⟩
  map f := ⟨Option.map f, rfl⟩
  map_id _ := Pointed.Hom.ext Option.map_id
map_comp _ _ := Pointed.Hom.ext by simp; rfl
-/
def typeToPointed : Type u ⥤ Pointed.{u} where
  obj X := ⟨Option X, none⟩
  map f := ⟨Option.map f, rfl⟩
  map_id _ := Pointed.Hom.ext Option.map_id
map_comp _ _ := Pointed.Hom.ext by simp; rfl

/--
Definition of `typeToPointedForgetAdjunction` / `typeToPointedForgetAdjunction` 的定义

English:
definition typeToPointedForgetAdjunction
  signature: : typeToPointed ⊣ forget Pointed
  body: Adjunction.mkOfHomEquiv {
    homEquiv := fun X Y =>
        { toFun := fun f => ↾(f.toFun ∘ Option.some)
          invFun := fun f => ⟨fun o => o.elim Y.point f, rfl⟩
          left_inv := fun f => by
            apply Pointed.Hom.ext
            funext x
            cases x
            · exact f.map_point.symm
            · rfl }
    homEquiv_naturality_left_symm := fun f g => by
      apply Pointed.Hom.ext
      funext x
      cases x <;> rfl }

中文:
定义 typeToPointedForgetAdjunction
  签名: : typeToPointed ⊣ forget Pointed
  定义体: Adjunction.mkOfHomEquiv {
    homEquiv := fun X Y =>
        { toFun := fun f => ↾(f.toFun ∘ Option.some)
          invFun := fun f => ⟨fun o => o.elim Y.point f, rfl⟩
          left_inv := fun f => by
            apply Pointed.Hom.ext
            funext x
            cases x
            · exact f.map_point.symm
            · rfl }
    homEquiv_naturality_left_symm := fun f g => by
      apply Pointed.Hom.ext
      funext x
      cases x <;> rfl }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, Option.some, Pointed, Pointed.Hom.ext, Y.point, f.map_point.symm, f.toFun, homEquiv, homEquiv_naturality_left_symm, invFun, left_inv, map_point, mkOfHomEquiv, o.elim
-/
def typeToPointedForgetAdjunction : typeToPointed ⊣ forget Pointed :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X Y =>
        { toFun := fun f => ↾(f.toFun ∘ Option.some)
          invFun := fun f => ⟨fun o => o.elim Y.point f, rfl⟩
          left_inv := fun f => by
            apply Pointed.Hom.ext
            funext x
            cases x
            · exact f.map_point.symm
            · rfl }
    homEquiv_naturality_left_symm := fun f g => by
      apply Pointed.Hom.ext
      funext x
      cases x <;> rfl }
