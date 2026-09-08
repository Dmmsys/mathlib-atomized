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

/-- The category of pointed types. -/
/-
**Pointed** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of pointed types.
-/
structure Pointed : Type (u + 1) where
  /-- the underlying type -/
  protected X : Type u
  /-- the distinguished element -/
  point : X

namespace Pointed

/-
**Pointed.** 是 Mathlib 中的一个实例，位于命名空间 `Pointed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort Pointed Type* :=
  ⟨Pointed.X⟩

/-- Turns a point into a pointed type. -/
/-
**Pointed.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `Pointed`。
形式化陈述：of {X : Type*} (point : X) : Pointed
参数：point : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turns a point into a pointed type.
-/
abbrev of {X : Type*} (point : X) : Pointed :=
  ⟨X, point⟩
/-
**Pointed.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `Pointed`。
形式化陈述：coe_of {X : Type*} (point : X) : ↥(of point) = X
参数：point : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of {X : Type*} (point : X) : ↥(of point) = X :=
  rfl

alias _root_.Prod.Pointed := of
/-
**Pointed.** 是 Mathlib 中的一个实例，位于命名空间 `Pointed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited Pointed :=
  ⟨of ((), ())⟩

/-- Morphisms in `Pointed`. -/
@[ext]
/-
**Pointed.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `Pointed`。
形式化陈述：Pointed → Pointed → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms in `Pointed`.
-/
protected structure Hom (X Y : Pointed.{u}) : Type u where
  /-- the underlying map -/
  toFun : X → Y
  /-- compatibility with the distinguished points -/
  map_point : toFun X.point = Y.point

namespace Hom

/-- The identity morphism of `X : Pointed`. -/
@[simps]
/-
**Pointed.Hom.id** 是 Mathlib 中的一个定义，位于命名空间 `Pointed.Hom`。
形式化陈述：id (X : Pointed) : Pointed.Hom X X
参数：X : Pointed。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity morphism of `X : Pointed`.
-/
def id (X : Pointed) : Pointed.Hom X X :=
  ⟨_root_.id, rfl⟩
/-
**Pointed.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `Pointed.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Pointed) : Inhabited (Pointed.Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms of `Pointed`. -/
@[simps]
/-
**Pointed.Hom.comp** 是 Mathlib 中的一个定义，位于命名空间 `Pointed.Hom`。
形式化陈述：comp {X Y Z : Pointed.{u}} (f : Pointed.Hom X Y) (g : Pointed.Hom Y Z) : P
ointed.Hom X Z
参数：f : Pointed.Hom X Y；g : Pointed.Hom Y Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of morphisms of `Pointed`.
-/
def comp {X Y Z : Pointed.{u}} (f : Pointed.Hom X Y) (g : Pointed.Hom Y Z) : Pointed.Hom X Z :=
  ⟨g.toFun ∘ f.toFun, by rw [Function.comp_apply, f.map_point, g.map_point]⟩

end Hom

/-
**Pointed.largeCategory** 是 Mathlib 中的一个实例，位于命名空间 `Pointed`。
形式化陈述：largeCategory : LargeCategory Pointed where Hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance largeCategory : LargeCategory Pointed where
  Hom := Pointed.Hom
  id := Hom.id
  comp := @Hom.comp
/-
**Pointed.Hom.id_toFun'** 是 Mathlib 中的一个定理，位于命名空间 `Pointed.Hom`。
形式化陈述：∀ (X : Pointed), (CategoryTheory.CategoryStruct.id X).toFun = id
参数：X : Pointed；CategoryTheory.CategoryStruct.id X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma Hom.id_toFun' (X : Pointed.{u}) : (𝟙 X : X ⟶ X).toFun = _root_.id := rfl
/-
**Pointed.Hom.comp_toFun'** 是 Mathlib 中的一个定理，位于命名空间 `Pointed.Hom`。
形式化陈述：∀ {X Y Z : Pointed} (f : X ⟶ Y) (g : Y ⟶ Z), (CategoryTheory.CategoryStruc
t.comp f g).toFun = g.toFun ∘ f.toFun
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma Hom.comp_toFun' {X Y Z : Pointed.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl
/-
**Pointed.** 是 Mathlib 中的一个实例，位于命名空间 `Pointed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : Pointed) : FunLike { f : X → Y // f X.point = Y.point } X Y where
  coe f := f
  coe_injective _ _ := Subtype.ext
/-
**Pointed.hasForget** 是 Mathlib 中的一个实例，位于命名空间 `Pointed`。
形式化陈述：hasForget : ConcreteCategory Pointed fun X Y => { f : X -> Y // f X.point 
= Y.point } where hom f
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Pointed.Hom.map_point`：∀ {X Y : Pointed} (self : X.Hom Y), self.toFun X.
point = Y.point
-/
instance hasForget : ConcreteCategory Pointed fun X Y => { f : X → Y // f X.point = Y.point } where
  hom f := ⟨f.1, f.2⟩
  ofHom f := ⟨f.1, f.2⟩

/-- Constructs an isomorphism between pointed types from an equivalence that preserves the point
between them. -/
@[simps]
/-
**Pointed.Iso.mk** 是 Mathlib 中的一个定义，位于命名空间 `Pointed.Iso`。
形式化陈述：{α β : Pointed} → (e : α.X ≃ β.X) → e α.point = β.point → (α ≅ β)
参数：e : α.X ≃ β.X；α ≅ β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Constructs an isomorphism between pointed types from an equivalence that preserv
es the point
between them.
-/
def Iso.mk {α β : Pointed} (e : α ≃ β) (he : e α.point = β.point) : α ≅ β where
  hom := ⟨e, he⟩
  inv := ⟨e.symm, e.symm_apply_eq.2 he.symm⟩
  hom_inv_id := Pointed.Hom.ext e.symm_comp_self
  inv_hom_id := Pointed.Hom.ext e.self_comp_symm

end Pointed

/-- `Option` as a functor from types to pointed types. This is the free functor. -/
@[simps]
/-
**typeToPointed** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：typeToPointed : Type u ⥤ Pointed.{u} where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Option` as a functor from types to pointed types. This is the free functor.
-/
def typeToPointed : Type u ⥤ Pointed.{u} where
  obj X := ⟨Option X, none⟩
  map f := ⟨Option.map f, rfl⟩
  map_id _ := Pointed.Hom.ext Option.map_id
  map_comp _ _ := Pointed.Hom.ext <| by simp; rfl

/-- `typeToPointed` is the free functor. -/
/-
**typeToPointedForgetAdjunction** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：typeToPointedForgetAdjunction : typeToPointed ⊣ forget Pointed
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`typeToPointed` is the free functor.
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
