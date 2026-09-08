/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Eilenberg-Moore (co)algebras for a (co)monad

This file defines Eilenberg-Moore (co)algebras for a (co)monad,
and provides the category instance for them.

Further it defines the adjoint pair of free and forgetful functors, respectively
from and to the original category, as well as the adjoint pair of forgetful and
cofree functors, respectively from and to the original category.

## References
* [Riehl, *Category theory in context*, Section 5.2.4][riehl2017]
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section


namespace CategoryTheory

open Category

universe v₁ u₁

-- morphism levels before object levels. See note [category_theory universes].
variable {C : Type u₁} [Category.{v₁} C]

namespace Monad

/-- An Eilenberg-Moore algebra for a monad `T`.
cf Definition 5.2.3 in [Riehl][riehl2017]. -/
/-
**CategoryTheory.Monad.Algebra** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.Monad`。
形式化陈述：Algebra (T : Monad C) : Type max u₁ v₁ where /-- The underlying object ass
ociated to an algebra. -/ A : C /-- The structure morphism associated to an alge
bra. -/ a : (T : C ⥤ C).obj A ⟶ A /-- The unit axiom associated to an algebra. -
/ unit : T.η.app A ≫ a = 𝟙 A
参数：T : Monad C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An Eilenberg-Moore algebra for a monad `T`.
cf Definition 5.2.3 in [Riehl][riehl2017].
-/
structure Algebra (T : Monad C) : Type max u₁ v₁ where
  /-- The underlying object associated to an algebra. -/
  A : C
  /-- The structure morphism associated to an algebra. -/
  a : (T : C ⥤ C).obj A ⟶ A
  /-- The unit axiom associated to an algebra. -/
  unit : T.η.app A ≫ a = 𝟙 A := by cat_disch
  /-- The associativity axiom associated to an algebra. -/
  assoc : T.μ.app A ≫ a = (T : C ⥤ C).map a ≫ a := by cat_disch

attribute [reassoc] Algebra.unit Algebra.assoc

namespace Algebra

variable {T : Monad C}

/-- A morphism of Eilenberg–Moore algebras for the monad `T`. -/
@[ext]
/-
**CategoryTheory.Monad.Algebra.Hom** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.Mon
ad.Algebra`。
形式化陈述：Hom (A B : Algebra T) where /-- The underlying morphism associated to a mo
rphism of algebras. -/ f : A.A ⟶ B.A /-- Compatibility with the structure morphi
sm, for a morphism of algebras. -/ h : (T : C ⥤ C).map f ≫ B.a = A.a ≫ f
参数：A B : Algebra T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of Eilenberg–Moore algebras for the monad `T`.
-/
structure Hom (A B : Algebra T) where
  /-- The underlying morphism associated to a morphism of algebras. -/
  f : A.A ⟶ B.A
  /-- Compatibility with the structure morphism, for a morphism of algebras. -/
  h : (T : C ⥤ C).map f ≫ B.a = A.a ≫ f := by cat_disch

attribute [reassoc (attr := simp)] Hom.h

namespace Hom

/-- The identity homomorphism for an Eilenberg–Moore algebra. -/
/-
**CategoryTheory.Monad.Algebra.Hom.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Monad.Algebra.Hom`。
形式化陈述：id (A : Algebra T) : Hom A A where f
参数：A : Algebra T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity homomorphism for an Eilenberg–Moore algebra.
-/
def id (A : Algebra T) : Hom A A where f := 𝟙 A.A
/-
**CategoryTheory.Monad.Algebra.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mo
nad.Algebra.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : Algebra T) : Inhabited (Hom A A) :=
  ⟨{ f := 𝟙 _ }⟩

/-- Composition of Eilenberg–Moore algebra homomorphisms. -/
/-
**CategoryTheory.Monad.Algebra.Hom.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Monad.Algebra.Hom`。
形式化陈述：comp {P Q R : Algebra T} (f : Hom P Q) (g : Hom Q R) : Hom P R where f
参数：f : Hom P Q；g : Hom Q R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of Eilenberg–Moore algebra homomorphisms.
-/
def comp {P Q R : Algebra T} (f : Hom P Q) (g : Hom Q R) : Hom P R where f := f.f ≫ g.f

end Hom

/-
**CategoryTheory.Monad.Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monad.
Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CategoryStruct (Algebra T) where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp _ _ _

@[ext]
/-
**CategoryTheory.Monad.Algebra.Hom.ext'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Monad.Algebra.Hom`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {T : CategoryT
heory.Monad C} (X Y : T.Algebra)   (f g : X ⟶ Y), f.f = g.f → f = g
参数：X Y : T.Algebra；f g : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Monad.Algebra.Hom.ext`：∀ {C : Type u₁} {inst : CategoryTh
eory.Category.{v₁, u₁} C} {T : CategoryTheory.Monad C} {A B : T.Algebra}   {x y 
: A.Hom B}, x.f = y.f → x …
-/
lemma Hom.ext' (X Y : Algebra T) (f g : X ⟶ Y) (h : f.f = g.f) : f = g := Hom.ext h

@[simp]
/-
**CategoryTheory.Monad.Algebra.comp_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Monad.Algebra`。
形式化陈述：comp_eq_comp {A A' A'' : Algebra T} (f : A ⟶ A') (g : A' ⟶ A'') : Algebra.
Hom.comp f g = f ≫ g
参数：f : A ⟶ A'；g : A' ⟶ A''。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_eq_comp {A A' A'' : Algebra T} (f : A ⟶ A') (g : A' ⟶ A'') :
    Algebra.Hom.comp f g = f ≫ g :=
  rfl

@[simp]
/-
**CategoryTheory.Monad.Algebra.id_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Monad.Algebra`。
形式化陈述：id_eq_id (A : Algebra T) : Algebra.Hom.id A = 𝟙 A
参数：A : Algebra T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_eq_id (A : Algebra T) : Algebra.Hom.id A = 𝟙 A :=
  rfl

@[simp]
/-
**CategoryTheory.Monad.Algebra.id_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Mo
nad.Algebra`。
形式化陈述：id_f (A : Algebra T) : (𝟙 A : A ⟶ A).f = 𝟙 A.A
参数：A : Algebra T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_f (A : Algebra T) : (𝟙 A : A ⟶ A).f = 𝟙 A.A :=
  rfl

@[simp]
/-
**CategoryTheory.Monad.Algebra.comp_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Monad.Algebra`。
形式化陈述：comp_f {A A' A'' : Algebra T} (f : A ⟶ A') (g : A' ⟶ A'') : (f ≫ g).f = f.
f ≫ g.f
参数：f : A ⟶ A'；g : A' ⟶ A''。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_f {A A' A'' : Algebra T} (f : A ⟶ A') (g : A' ⟶ A'') : (f ≫ g).f = f.f ≫ g.f :=
  rfl

/-- The category of Eilenberg-Moore algebras for a monad.
cf Definition 5.2.4 in [Riehl][riehl2017]. -/
/-
**CategoryTheory.Monad.Algebra.eilenbergMoore** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Monad.Algebra`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {T : C
ategoryTheory.Monad C} → CategoryTheory.Category.{v₁, max u₁ v₁} T.Algebra
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of Eilenberg-Moore algebras for a monad.
cf Definition 5.2.4 in [Riehl][riehl2017].
-/
instance eilenbergMoore : Category (Algebra T) where

/--
To construct an isomorphism of algebras, it suffices to give an isomorphism of the carriers which
commutes with the structure morphisms.
-/
@[simps]
/-
**CategoryTheory.Monad.Algebra.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.M
onad.Algebra`。
形式化陈述：isoMk {A B : Algebra T} (h : A.A ≅ B.A) (w : (T : C ⥤ C).map h.hom ≫ B.a =
 A.a ≫ h.hom
参数：h : A.A ≅ B.A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To construct an isomorphism of algebras, it suffices to give an isomorphism of t
he carriers which
commutes with the structure morphisms.
-/
def isoMk {A B : Algebra T} (h : A.A ≅ B.A)
    (w : (T : C ⥤ C).map h.hom ≫ B.a = A.a ≫ h.hom := by cat_disch) : A ≅ B where
  hom := { f := h.hom }
  inv :=
    { f := h.inv
      h := by
        rw [h.eq_comp_inv, Category.assoc, ← w, ← Functor.map_comp_assoc]
        simp }

end Algebra

variable (T : Monad C)

/-- The forgetful functor from the Eilenberg-Moore category, forgetting the algebraic structure. -/
@[simps]
/-
**CategoryTheory.Monad.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Monad`。
形式化陈述：forget : Algebra T ⥤ C where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from the Eilenberg-Moore category, forgetting the algebrai
c structure.
-/
def forget : Algebra T ⥤ C where
  obj A := A.A
  map f := f.f

/-- The free functor from the Eilenberg-Moore category, constructing an algebra for any object. -/
@[simps]
/-
**CategoryTheory.Monad.free** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Monad`。
形式化陈述：free : C ⥤ Algebra T where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free functor from the Eilenberg-Moore category, constructing an algebra for 
any object.
-/
def free : C ⥤ Algebra T where
  obj X :=
    { A := T.obj X
      a := T.μ.app X
      assoc := (T.assoc _).symm }
  map f :=
    { f := T.map f
      h := T.μ.naturality _ }
/-
**CategoryTheory.Monad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited C] : Inhabited (Algebra T) :=
  ⟨(free T).obj default⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- The other two `simps` projection lemmas can be derived from these two, so `simp_nf` complains if
-- those are added too
/-- The adjunction between the free and forgetful constructions for Eilenberg-Moore algebras for
  a monad. cf Lemma 5.2.8 of [Riehl][riehl2017]. -/
@[simps! unit counit]
/-
**CategoryTheory.Monad.adj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Monad`。
形式化陈述：adj : T.free ⊣ T.forget
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction between the free and forgetful constructions for Eilenberg-Moore 
algebras for
  a monad. cf Lemma 5.2.8 of [Riehl][riehl2017].
-/
def adj : T.free ⊣ T.forget :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => T.η.app X ≫ f.f
          invFun := fun f =>
            { f := T.map f ≫ Y.a
              h := by simp [← Y.assoc, ← T.μ.naturality_assoc] }
          left_inv := fun f => by
            ext
            simp
          right_inv := fun f => by
            dsimp only [forget_obj]
            rw [← T.η.naturality_assoc, Y.unit]
            apply Category.comp_id } }

/-- Given an algebra morphism whose carrier part is an isomorphism, we get an algebra isomorphism.
-/
/-
**CategoryTheory.Monad.algebra_iso_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Monad`。
形式化陈述：algebra_iso_of_iso {A B : Algebra T} (f : A ⟶ B) [IsIso f.f] : IsIso f
参数：f : A ⟶ B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Monad.Algebra.Hom.h`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {T : CategoryTheory.Monad C} {A B : T.Algebra}   (self :
 A.Hom B),   CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Monad.Algebra.Hom.ext'`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {T : CategoryTheory.Monad C} (X Y : T.Algebra)   (f g
 : X ⟶ Y), f.f = g.f → f = …
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y

--- 原说明 ---
Given an algebra morphism whose carrier part is an isomorphism, we get an algebr
a isomorphism.
-/
theorem algebra_iso_of_iso {A B : Algebra T} (f : A ⟶ B) [IsIso f.f] : IsIso f :=
  ⟨⟨{ f := inv f.f, h := by simp }, by cat_disch⟩⟩
/-
**CategoryTheory.Monad.forget_reflects_iso** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Monad`。
形式化陈述：forget_reflects_iso : T.forget.ReflectsIsomorphisms where reflects {_ _} f
 [IsIso f.f]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Monad.algebra_iso_of_iso`：algebra_iso_of_iso {A B : Algeb
ra T} (f : A ⟶ B) [IsIso f.f] : IsIso f
-/
instance forget_reflects_iso : T.forget.ReflectsIsomorphisms where
  reflects {_ _} f [IsIso f.f] := algebra_iso_of_iso T f
/-
**CategoryTheory.Monad.forget_faithful** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Monad`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (T : CategoryT
heory.Monad C), T.forget.Faithful
参数：T : CategoryTheory.Monad C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Monad.Algebra.Hom.ext'`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {T : CategoryTheory.Monad C} (X Y : T.Algebra)   (f g
 : X ⟶ Y), f.f = g.f → f = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance forget_faithful : T.forget.Faithful where

/-- Given an algebra morphism whose carrier part is an epimorphism, we get an algebra epimorphism.
-/
/-
**CategoryTheory.Monad.algebra_epi_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Monad`。
形式化陈述：algebra_epi_of_epi {X Y : Algebra T} (f : X ⟶ Y) [h : Epi f.f] : Epi f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.epi_of_epi_map`：epi_of_epi_map (F : C ⥤ D) [Refle
ctsEpimorphisms F] {X Y : C} {f : X ⟶ Y} (h : Epi (F.map f)) : Epi f
· 使用定理 `CategoryTheory.Functor.reflectsEpimorphisms_of_faithful`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Monad.forget_faithful`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] (T : CategoryTheory.Monad C), T.forget.Faithful

--- 原说明 ---
Given an algebra morphism whose carrier part is an epimorphism, we get an algebr
a epimorphism.
-/
theorem algebra_epi_of_epi {X Y : Algebra T} (f : X ⟶ Y) [h : Epi f.f] : Epi f :=
  (forget T).epi_of_epi_map h

/-- Given an algebra morphism whose carrier part is a monomorphism, we get an algebra monomorphism.
-/
/-
**CategoryTheory.Monad.algebra_mono_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Monad`。
形式化陈述：algebra_mono_of_mono {X Y : Algebra T} (f : X ⟶ Y) [h : Mono f.f] : Mono f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.mono_of_mono_map`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.reflectsMonomorphisms_of_faithful`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Monad.forget_faithful`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] (T : CategoryTheory.Monad C), T.forget.Faithful

--- 原说明 ---
Given an algebra morphism whose carrier part is a monomorphism, we get an algebr
a monomorphism.
-/
theorem algebra_mono_of_mono {X Y : Algebra T} (f : X ⟶ Y) [h : Mono f.f] : Mono f :=
  (forget T).mono_of_mono_map h
/-
**CategoryTheory.Monad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : T.forget.IsRightAdjoint :=
  ⟨T.free, ⟨T.adj⟩⟩

/--
Given a monad morphism from `T₂` to `T₁`, we get a functor from the algebras of `T₁` to algebras of
`T₂`.
-/
@[simps]
/-
**CategoryTheory.Monad.algebraFunctorOfMonadHom** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Monad`。
形式化陈述：algebraFunctorOfMonadHom {T₁ T₂ : Monad C} (h : T₂ ⟶ T₁) : Algebra T₁ ⥤ Al
gebra T₂ where obj A
参数：h : T₂ ⟶ T₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a monad morphism from `T₂` to `T₁`, we get a functor from the algebras of 
`T₁` to algebras of
`T₂`.
-/
def algebraFunctorOfMonadHom {T₁ T₂ : Monad C} (h : T₂ ⟶ T₁) : Algebra T₁ ⥤ Algebra T₂ where
  obj A :=
    { A := A.A
      a := h.app A.A ≫ A.a
      unit := by simp [A.unit]
      assoc := by simp [A.assoc] }
  map f := { f := f.f }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
The identity monad morphism induces the identity functor from the category of algebras to itself.
-/
@[simps (rhsMd := .default)]
/-
**CategoryTheory.Monad.algebraFunctorOfMonadHomId** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Monad`。
形式化陈述：algebraFunctorOfMonadHomId {T₁ : Monad C} : algebraFunctorOfMonadHom (𝟙 T₁
) ≅ 𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity monad morphism induces the identity functor from the category of al
gebras to itself.
-/
def algebraFunctorOfMonadHomId {T₁ : Monad C} : algebraFunctorOfMonadHom (𝟙 T₁) ≅ 𝟭 _ :=
  NatIso.ofComponents fun X => Algebra.isoMk (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A composition of monad morphisms gives the composition of corresponding functors.
-/
@[simps (rhsMd := .default)]
/-
**CategoryTheory.Monad.algebraFunctorOfMonadHomComp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Monad`。
形式化陈述：algebraFunctorOfMonadHomComp {T₁ T₂ T₃ : Monad C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ 
T₃) : algebraFunctorOfMonadHom (f ≫ g) ≅ algebraFunctorOfMonadHom g ⋙ algebraFun
ctorOfMonadHom f
参数：f : T₁ ⟶ T₂；g : T₂ ⟶ T₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A composition of monad morphisms gives the composition of corresponding functors
.
-/
def algebraFunctorOfMonadHomComp {T₁ T₂ T₃ : Monad C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    algebraFunctorOfMonadHom (f ≫ g) ≅ algebraFunctorOfMonadHom g ⋙ algebraFunctorOfMonadHom f :=
  NatIso.ofComponents fun X => Algebra.isoMk (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
/-- If `f` and `g` are two equal morphisms of monads, then the functors of algebras induced by them
are isomorphic.
We define it like this as opposed to using `eqToIso` so that the components are nicer to prove
lemmas about.
-/
@[simps (rhsMd := .default)]
/-
**CategoryTheory.Monad.algebraFunctorOfMonadHomEq** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Monad`。
形式化陈述：algebraFunctorOfMonadHomEq {T₁ T₂ : Monad C} {f g : T₁ ⟶ T₂} (h : f = g) :
 algebraFunctorOfMonadHom f ≅ algebraFunctorOfMonadHom g
参数：h : f = g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` and `g` are two equal morphisms of monads, then the functors of algebras 
induced by them
are isomorphic.
We define it like this as opposed to using `eqToIso` so that the components are 
nicer to prove
lemmas about.
-/
def algebraFunctorOfMonadHomEq {T₁ T₂ : Monad C} {f g : T₁ ⟶ T₂} (h : f = g) :
    algebraFunctorOfMonadHom f ≅ algebraFunctorOfMonadHom g :=
  NatIso.ofComponents fun X => Algebra.isoMk (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Isomorphic monads give equivalent categories of algebras. Furthermore, they are equivalent as
categories over `C`, that is, we have `algebraEquivOfIsoMonads h ⋙ forget = forget`.
-/
@[simps]
/-
**CategoryTheory.Monad.algebraEquivOfIsoMonads** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Monad`。
形式化陈述：algebraEquivOfIsoMonads {T₁ T₂ : Monad C} (h : T₁ ≅ T₂) : Algebra T₁ ≌ Alg
ebra T₂ where functor
参数：h : T₁ ≅ T₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphic monads give equivalent categories of algebras. Furthermore, they are 
equivalent as
categories over `C`, that is, we have `algebraEquivOfIsoMonads h ⋙ forget = forg
et`.
-/
def algebraEquivOfIsoMonads {T₁ T₂ : Monad C} (h : T₁ ≅ T₂) : Algebra T₁ ≌ Algebra T₂ where
  functor := algebraFunctorOfMonadHom h.inv
  inverse := algebraFunctorOfMonadHom h.hom
  unitIso :=
    algebraFunctorOfMonadHomId.symm ≪≫
      algebraFunctorOfMonadHomEq (by simp) ≪≫ algebraFunctorOfMonadHomComp _ _
  counitIso :=
    (algebraFunctorOfMonadHomComp _ _).symm ≪≫
      algebraFunctorOfMonadHomEq (by simp) ≪≫ algebraFunctorOfMonadHomId

@[simp]
/-
**CategoryTheory.Monad.algebra_equiv_of_iso_monads_comp_forget** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Monad`。
形式化陈述：algebra_equiv_of_iso_monads_comp_forget {T₁ T₂ : Monad C} (h : T₁ ⟶ T₂) : 
algebraFunctorOfMonadHom h ⋙ forget _ = forget _
参数：h : T₁ ⟶ T₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebra_equiv_of_iso_monads_comp_forget {T₁ T₂ : Monad C} (h : T₁ ⟶ T₂) :
    algebraFunctorOfMonadHom h ⋙ forget _ = forget _ :=
  rfl

end Monad

namespace Comonad

/-- An Eilenberg-Moore coalgebra for a comonad `T`. -/
/-
**CategoryTheory.Comonad.Coalgebra** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.Com
onad`。
形式化陈述：Coalgebra (G : Comonad C) : Type max u₁ v₁ where /-- The underlying object
 associated to a coalgebra. -/ A : C /-- The structure morphism associated to a 
coalgebra. -/ a : A ⟶ (G : C ⥤ C).obj A /-- The counit axiom associated to a coa
lgebra. -/ counit : a ≫ G.ε.app A = 𝟙 A
参数：G : Comonad C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An Eilenberg-Moore coalgebra for a comonad `T`.
-/
structure Coalgebra (G : Comonad C) : Type max u₁ v₁ where
  /-- The underlying object associated to a coalgebra. -/
  A : C
  /-- The structure morphism associated to a coalgebra. -/
  a : A ⟶ (G : C ⥤ C).obj A
  /-- The counit axiom associated to a coalgebra. -/
  counit : a ≫ G.ε.app A = 𝟙 A := by cat_disch
  /-- The coassociativity axiom associated to a coalgebra. -/
  coassoc : a ≫ G.δ.app A = a ≫ G.map a := by cat_disch


attribute [reassoc] Coalgebra.counit Coalgebra.coassoc

namespace Coalgebra

variable {G : Comonad C}

/-- A morphism of Eilenberg-Moore coalgebras for the comonad `G`. -/
@[ext]
/-
**CategoryTheory.Comonad.Coalgebra.Hom** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory
.Comonad.Coalgebra`。
形式化陈述：Hom (A B : Coalgebra G) where /-- The underlying morphism associated to a 
morphism of coalgebras. -/ f : A.A ⟶ B.A /-- Compatibility with the structure mo
rphism, for a morphism of coalgebras. -/ h : A.a ≫ (G : C ⥤ C).map f = f ≫ B.a
参数：A B : Coalgebra G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of Eilenberg-Moore coalgebras for the comonad `G`.
-/
structure Hom (A B : Coalgebra G) where
  /-- The underlying morphism associated to a morphism of coalgebras. -/
  f : A.A ⟶ B.A
  /-- Compatibility with the structure morphism, for a morphism of coalgebras. -/
  h : A.a ≫ (G : C ⥤ C).map f = f ≫ B.a := by cat_disch

attribute [reassoc (attr := simp)] Hom.h

namespace Hom

/-- The identity homomorphism for an Eilenberg–Moore coalgebra. -/
/-
**CategoryTheory.Comonad.Coalgebra.Hom.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Comonad.Coalgebra.Hom`。
形式化陈述：id (A : Coalgebra G) : Hom A A where f
参数：A : Coalgebra G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity homomorphism for an Eilenberg–Moore coalgebra.
-/
def id (A : Coalgebra G) : Hom A A where f := 𝟙 A.A

/-- Composition of Eilenberg–Moore coalgebra homomorphisms. -/
/-
**CategoryTheory.Comonad.Coalgebra.Hom.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Comonad.Coalgebra.Hom`。
形式化陈述：comp {P Q R : Coalgebra G} (f : Hom P Q) (g : Hom Q R) : Hom P R where f
参数：f : Hom P Q；g : Hom Q R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of Eilenberg–Moore coalgebra homomorphisms.
-/
def comp {P Q R : Coalgebra G} (f : Hom P Q) (g : Hom Q R) : Hom P R where f := f.f ≫ g.f

end Hom

/-- The category of Eilenberg-Moore coalgebras for a comonad. -/
/-
**CategoryTheory.Comonad.Coalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Co
monad.Coalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of Eilenberg-Moore coalgebras for a comonad.
-/
instance : CategoryStruct (Coalgebra G) where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp _ _ _

@[ext]
/-
**CategoryTheory.Comonad.Coalgebra.Hom.ext'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Comonad.Coalgebra.Hom`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {G : CategoryT
heory.Comonad C} (X Y : G.Coalgebra)   (f g : X ⟶ Y), f.f = g.f → f = g
参数：X Y : G.Coalgebra；f g : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Comonad.Coalgebra.Hom.ext`：∀ {C : Type u₁} {inst : Catego
ryTheory.Category.{v₁, u₁} C} {G : CategoryTheory.Comonad C} {A B : G.Coalgebra}
   {x y : A.Hom B}, x.f = y.f …
-/
lemma Hom.ext' (X Y : Coalgebra G) (f g : X ⟶ Y) (h : f.f = g.f) : f = g := Hom.ext h

@[simp]
/-
**CategoryTheory.Comonad.Coalgebra.comp_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Comonad.Coalgebra`。
形式化陈述：comp_eq_comp {A A' A'' : Coalgebra G} (f : A ⟶ A') (g : A' ⟶ A'') : Coalge
bra.Hom.comp f g = f ≫ g
参数：f : A ⟶ A'；g : A' ⟶ A''。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_eq_comp {A A' A'' : Coalgebra G} (f : A ⟶ A') (g : A' ⟶ A'') :
    Coalgebra.Hom.comp f g = f ≫ g :=
  rfl

@[simp]
/-
**CategoryTheory.Comonad.Coalgebra.id_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Comonad.Coalgebra`。
形式化陈述：id_eq_id (A : Coalgebra G) : Coalgebra.Hom.id A = 𝟙 A
参数：A : Coalgebra G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_eq_id (A : Coalgebra G) : Coalgebra.Hom.id A = 𝟙 A :=
  rfl

@[simp]
/-
**CategoryTheory.Comonad.Coalgebra.id_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Comonad.Coalgebra`。
形式化陈述：id_f (A : Coalgebra G) : (𝟙 A : A ⟶ A).f = 𝟙 A.A
参数：A : Coalgebra G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_f (A : Coalgebra G) : (𝟙 A : A ⟶ A).f = 𝟙 A.A :=
  rfl

@[simp]
/-
**CategoryTheory.Comonad.Coalgebra.comp_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Comonad.Coalgebra`。
形式化陈述：comp_f {A A' A'' : Coalgebra G} (f : A ⟶ A') (g : A' ⟶ A'') : (f ≫ g).f = 
f.f ≫ g.f
参数：f : A ⟶ A'；g : A' ⟶ A''。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_f {A A' A'' : Coalgebra G} (f : A ⟶ A') (g : A' ⟶ A'') : (f ≫ g).f = f.f ≫ g.f :=
  rfl

/-- The category of Eilenberg-Moore coalgebras for a comonad. -/
/-
**CategoryTheory.Comonad.Coalgebra.eilenbergMoore** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Comonad.Coalgebra`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {G : C
ategoryTheory.Comonad C} → CategoryTheory.Category.{v₁, max u₁ v₁} G.Coalgebra
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of Eilenberg-Moore coalgebras for a comonad.
-/
instance eilenbergMoore : Category (Coalgebra G) where

/--
To construct an isomorphism of coalgebras, it suffices to give an isomorphism of the carriers which
commutes with the structure morphisms.
-/
@[simps]
/-
**CategoryTheory.Comonad.Coalgebra.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Comonad.Coalgebra`。
形式化陈述：isoMk {A B : Coalgebra G} (h : A.A ≅ B.A) (w : A.a ≫ (G : C ⥤ C).map h.hom
 = h.hom ≫ B.a
参数：h : A.A ≅ B.A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To construct an isomorphism of coalgebras, it suffices to give an isomorphism of
 the carriers which
commutes with the structure morphisms.
-/
def isoMk {A B : Coalgebra G} (h : A.A ≅ B.A)
    (w : A.a ≫ (G : C ⥤ C).map h.hom = h.hom ≫ B.a := by cat_disch) : A ≅ B where
  hom := { f := h.hom }
  inv :=
    { f := h.inv
      h := by
        rw [h.eq_inv_comp, ← reassoc_of% w, ← Functor.map_comp]
        simp }

end Coalgebra

variable (G : Comonad C)

/-- The forgetful functor from the Eilenberg-Moore category, forgetting the coalgebraic
structure. -/
@[simps]
/-
**CategoryTheory.Comonad.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comona
d`。
形式化陈述：forget : Coalgebra G ⥤ C where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from the Eilenberg-Moore category, forgetting the coalgebr
aic
structure.
-/
def forget : Coalgebra G ⥤ C where
  obj A := A.A
  map f := f.f

/-- The cofree functor from the Eilenberg-Moore category, constructing a coalgebra for any
object. -/
@[simps]
/-
**CategoryTheory.Comonad.cofree** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comona
d`。
形式化陈述：cofree : C ⥤ Coalgebra G where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofree functor from the Eilenberg-Moore category, constructing a coalgebra f
or any
object.
-/
def cofree : C ⥤ Coalgebra G where
  obj X :=
    { A := G.obj X
      a := G.δ.app X
      coassoc := (G.coassoc _).symm }
  map f :=
    { f := G.map f
      h := (G.δ.naturality _).symm }

set_option backward.isDefEq.respectTransparency false in
-- The other two `simps` projection lemmas can be derived from these two, so `simp_nf` complains if
-- those are added too
/-- The adjunction between the cofree and forgetful constructions for Eilenberg-Moore coalgebras
for a comonad.
-/
@[simps! unit counit]
/-
**CategoryTheory.Comonad.adj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comonad`。
形式化陈述：adj : G.forget ⊣ G.cofree
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction between the cofree and forgetful constructions for Eilenberg-Moor
e coalgebras
for a comonad.
-/
def adj : G.forget ⊣ G.cofree :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f =>
            { f := X.a ≫ G.map f
              h := by simp [← Coalgebra.coassoc_assoc] }
          invFun := fun g => g.f ≫ G.ε.app Y
          left_inv := fun f => by
            dsimp
            rw [Category.assoc, G.ε.naturality, Functor.id_map, X.counit_assoc]
          right_inv := fun g => by
            ext1; dsimp
            rw [Functor.map_comp, g.h_assoc, cofree_obj_a, Comonad.right_counit]
            apply comp_id } }

/-- Given a coalgebra morphism whose carrier part is an isomorphism, we get a coalgebra isomorphism.
-/
/-
**CategoryTheory.Comonad.coalgebra_iso_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Comonad`。
形式化陈述：coalgebra_iso_of_iso {A B : Coalgebra G} (f : A ⟶ B) [IsIso f.f] : IsIso f
参数：f : A ⟶ B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.eq_inv_comp`：eq_inv_comp (α : X ⟶ Y) [IsIso α] {f :
 X ⟶ Z} {g : Y ⟶ Z} : g = inv α ≫ f ↔ α ≫ g = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Comonad.Coalgebra.Hom.h_assoc`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {G : CategoryTheory.Comonad C} {A B : G.Coalge
bra}   (self : A.Hom B) {Z : C} (h…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Comonad.Coalgebra.Hom.ext'`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {G : CategoryTheory.Comonad C} (X Y : G.Coalgebra
)   (f g : X ⟶ Y), f.f = g.f → …
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y

--- 原说明 ---
Given a coalgebra morphism whose carrier part is an isomorphism, we get a coalge
bra isomorphism.
-/
theorem coalgebra_iso_of_iso {A B : Coalgebra G} (f : A ⟶ B) [IsIso f.f] : IsIso f :=
  ⟨⟨{   f := inv f.f
        h := by
          rw [IsIso.eq_inv_comp f.f, ← f.h_assoc]
          simp },
      by cat_disch⟩⟩
/-
**CategoryTheory.Comonad.forget_reflects_iso** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Comonad`。
形式化陈述：forget_reflects_iso : G.forget.ReflectsIsomorphisms where reflects {_ _} f
 [IsIso f.f]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Comonad.coalgebra_iso_of_iso`：coalgebra_iso_of_iso {A B :
 Coalgebra G} (f : A ⟶ B) [IsIso f.f] : IsIso f
-/
instance forget_reflects_iso : G.forget.ReflectsIsomorphisms where
  reflects {_ _} f [IsIso f.f] := coalgebra_iso_of_iso G f
/-
**CategoryTheory.Comonad.forget_faithful** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Comonad`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (G : CategoryT
heory.Comonad C), G.forget.Faithful
参数：G : CategoryTheory.Comonad C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Comonad.Coalgebra.Hom.ext'`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {G : CategoryTheory.Comonad C} (X Y : G.Coalgebra
)   (f g : X ⟶ Y), f.f = g.f → …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance forget_faithful : (forget G).Faithful where

/-- Given a coalgebra morphism whose carrier part is an epimorphism, we get an algebra epimorphism.
-/
/-
**CategoryTheory.Comonad.algebra_epi_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Comonad`。
形式化陈述：algebra_epi_of_epi {X Y : Coalgebra G} (f : X ⟶ Y) [h : Epi f.f] : Epi f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.epi_of_epi_map`：epi_of_epi_map (F : C ⥤ D) [Refle
ctsEpimorphisms F] {X Y : C} {f : X ⟶ Y} (h : Epi (F.map f)) : Epi f
· 使用定理 `CategoryTheory.Functor.reflectsEpimorphisms_of_faithful`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Comonad.forget_faithful`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] (G : CategoryTheory.Comonad C), G.forget.Faithful

--- 原说明 ---
Given a coalgebra morphism whose carrier part is an epimorphism, we get an algeb
ra epimorphism.
-/
theorem algebra_epi_of_epi {X Y : Coalgebra G} (f : X ⟶ Y) [h : Epi f.f] : Epi f :=
  (forget G).epi_of_epi_map h

/-- Given a coalgebra morphism whose carrier part is a monomorphism, we get an algebra monomorphism.
-/
/-
**CategoryTheory.Comonad.algebra_mono_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Comonad`。
形式化陈述：algebra_mono_of_mono {X Y : Coalgebra G} (f : X ⟶ Y) [h : Mono f.f] : Mono
 f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.mono_of_mono_map`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.reflectsMonomorphisms_of_faithful`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Comonad.forget_faithful`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] (G : CategoryTheory.Comonad C), G.forget.Faithful

--- 原说明 ---
Given a coalgebra morphism whose carrier part is a monomorphism, we get an algeb
ra monomorphism.
-/
theorem algebra_mono_of_mono {X Y : Coalgebra G} (f : X ⟶ Y) [h : Mono f.f] : Mono f :=
  (forget G).mono_of_mono_map h
/-
**CategoryTheory.Comonad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comonad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : G.forget.IsLeftAdjoint :=
  ⟨_, ⟨G.adj⟩⟩

end Comonad

end CategoryTheory

