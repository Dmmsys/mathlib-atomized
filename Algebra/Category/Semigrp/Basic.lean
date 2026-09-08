/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
module

public import Mathlib.Algebra.PEmptyInstances
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Category instances for `Mul`, `Add`, `Semigroup` and `AddSemigroup`

We introduce the bundled categories:
* `MagmaCat`
* `AddMagmaCat`
* `Semigrp`
* `AddSemigrp`

along with the relevant forgetful functors between them.

This closely follows `Mathlib/Algebra/Category/MonCat/Basic.lean`.

## TODO

* Limits in these categories
* free/forgetful adjunctions
-/

@[expose] public section


universe u v

open CategoryTheory

/-- The category of additive magmas and additive magma morphisms. -/
/-
**AddMagmaCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of additive magmas and additive magma morphisms.
-/
structure AddMagmaCat : Type (u + 1) where
  /-- The underlying additive magma. -/
  (carrier : Type u)
  [str : Add carrier]

/-- The category of magmas and magma morphisms. -/
@[to_additive]
/-
**MagmaCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of magmas and magma morphisms.
-/
structure MagmaCat : Type (u + 1) where
  /-- The underlying magma. -/
  (carrier : Type u)
  [str : Mul carrier]

attribute [instance] AddMagmaCat.str MagmaCat.str

initialize_simps_projections AddMagmaCat (carrier → coe, -str)
initialize_simps_projections MagmaCat (carrier → coe, -str)

namespace MagmaCat

@[to_additive]
/-
**MagmaCat.** 是 Mathlib 中的一个实例，位于命名空间 `MagmaCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort MagmaCat (Type u) :=
  ⟨MagmaCat.carrier⟩

attribute [coe] AddMagmaCat.carrier MagmaCat.carrier

/-- Construct a bundled `MagmaCat` from the underlying type and typeclass. -/
@[to_additive /-- Construct a bundled `AddMagmaCat` from the underlying type and typeclass. -/]
/-
**MagmaCat.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `MagmaCat`。
形式化陈述：of (M : Type u) [Mul M] : MagmaCat
参数：M : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `MagmaCat` from the underlying type and typeclass.
-/
abbrev of (M : Type u) [Mul M] : MagmaCat := ⟨M⟩

end MagmaCat

/-- The type of morphisms in `AddMagmaCat R`. -/
@[ext]
/-
**AddMagmaCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `AddMagmaCat`。
形式化陈述：AddMagmaCat → AddMagmaCat → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `AddMagmaCat R`.
-/
structure AddMagmaCat.Hom (A B : AddMagmaCat.{u}) where
  private mk ::
  /-- The underlying `AddHom`. -/
  hom' : A →ₙ+ B

/-- The type of morphisms in `MagmaCat R`. -/
@[to_additive, ext]
/-
**MagmaCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `MagmaCat`。
形式化陈述：MagmaCat → MagmaCat → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `MagmaCat R`.
-/
structure MagmaCat.Hom (A B : MagmaCat.{u}) where
  private mk ::
  /-- The underlying `MulHom`. -/
  hom' : A →ₙ* B

namespace MagmaCat

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/-
**MagmaCat.** 是 Mathlib 中的一个实例，位于命名空间 `MagmaCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category MagmaCat.{u} where
  Hom X Y := Hom X Y
  id X := ⟨MulHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/-
**MagmaCat.** 是 Mathlib 中的一个实例，位于命名空间 `MagmaCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory MagmaCat (· →ₙ* ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `MagmaCat` back into a `MulHom`. -/
@[to_additive /-- Turn a morphism in `AddMagmaCat` back into an `AddHom`. -/]
/-
**MagmaCat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `MagmaCat.Hom`。
形式化陈述：{X Y : MagmaCat} → X.Hom Y → ↑X →ₙ* ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `MagmaCat` back into a `MulHom`.
-/
abbrev Hom.hom {X Y : MagmaCat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := MagmaCat) f

/-- Typecheck a `MulHom` as a morphism in `MagmaCat`. -/
@[to_additive /-- Typecheck an `AddHom` as a morphism in `AddMagmaCat`. -/]
/-
**MagmaCat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `MagmaCat`。
形式化陈述：ofHom {X Y : Type u} [Mul X] [Mul Y] (f : X ->ₙ* Y) : of X ⟶ of Y
参数：f : X ->ₙ* Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `MulHom` as a morphism in `MagmaCat`.
-/
abbrev ofHom {X Y : Type u} [Mul X] [Mul Y] (f : X →ₙ* Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := MagmaCat) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**MagmaCat.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `MagmaCat.Hom.Simps`。
形式化陈述：(X Y : MagmaCat) → X.Hom Y → ↑X →ₙ* ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (X Y : MagmaCat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)
initialize_simps_projections AddMagmaCat.Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[to_additive (attr := simp)]
/-
**MagmaCat.coe_id** 是 Mathlib 中的一个引理，位于命名空间 `MagmaCat`。
形式化陈述：coe_id {X : MagmaCat} : (𝟙 X : X -> X) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma coe_id {X : MagmaCat} : (𝟙 X : X → X) = id := rfl

@[to_additive (attr := simp)]
/-
**MagmaCat.coe_comp** 是 Mathlib 中的一个引理，位于命名空间 `MagmaCat`。
形式化陈述：coe_comp {X Y Z : MagmaCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g
 ∘ f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comp {X Y Z : MagmaCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[deprecated (since := "2026-02-10")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[to_additive (attr := ext)]
/-
**MagmaCat.ext** 是 Mathlib 中的一个引理，位于命名空间 `MagmaCat`。
形式化陈述：ext {X Y : MagmaCat} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g
参数：w : forall x : X, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
-/
lemma ext {X Y : MagmaCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[to_additive]
-- This is not `simp` to avoid rewriting in types of terms.
/-
**MagmaCat.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `MagmaCat`。
形式化陈述：coe_of (M : Type u) [Mul M] : (MagmaCat.of M : Type u) = M
参数：M : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (M : Type u) [Mul M] : (MagmaCat.of M : Type u) = M := rfl

@[to_additive (attr := simp)]
/-
**MagmaCat.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `MagmaCat`。
形式化陈述：hom_id {M : MagmaCat} : (𝟙 M : M ⟶ M).hom = MulHom.id M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_id {M : MagmaCat} : (𝟙 M : M ⟶ M).hom = MulHom.id M := rfl

/- Provided for rewriting. -/
@[to_additive]
/-
**MagmaCat.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `MagmaCat`。
形式化陈述：id_apply (M : MagmaCat) (x : M) : (𝟙 M : M ⟶ M) x = x
参数：M : MagmaCat；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulHom.id_apply`：∀ (M : Type u_10) [inst : Mul M] (x : M), (MulHom.id M)
 x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (M : MagmaCat) (x : M) :
    (𝟙 M : M ⟶ M) x = x := by simp

@[to_additive (attr := simp)]
/-
**MagmaCat.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `MagmaCat`。
形式化陈述：hom_comp {M N T : MagmaCat} (f : M ⟶ N) (g : N ⟶ T) : (f ≫ g).hom = g.hom.
comp f.hom
参数：f : M ⟶ N；g : N ⟶ T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {M N T : MagmaCat} (f : M ⟶ N) (g : N ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
@[to_additive]
/-
**MagmaCat.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `MagmaCat`。
形式化陈述：comp_apply {M N T : MagmaCat} (f : M ⟶ N) (g : N ⟶ T) (x : M) : (f ≫ g) x 
= g (f x)
参数：f : M ⟶ N；g : N ⟶ T；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {M N T : MagmaCat} (f : M ⟶ N) (g : N ⟶ T) (x : M) :
    (f ≫ g) x = g (f x) := by simp

@[to_additive (attr := ext)]
/-
**MagmaCat.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `MagmaCat`。
形式化陈述：hom_ext {M N : MagmaCat} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MagmaCat.Hom.ext`：∀ {A B : MagmaCat} {x y : A.Hom B}, x.hom' = y.hom' → 
x = y
-/
lemma hom_ext {M N : MagmaCat} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[to_additive (attr := simp)]
/-
**MagmaCat.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `MagmaCat`。
形式化陈述：hom_ofHom {M N : Type u} [Mul M] [Mul N] (f : M ->ₙ* N) : (ofHom f).hom = 
f
参数：f : M ->ₙ* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {M N : Type u} [Mul M] [Mul N] (f : M →ₙ* N) : (ofHom f).hom = f := rfl

@[to_additive (attr := simp)]
/-
**MagmaCat.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `MagmaCat`。
形式化陈述：ofHom_hom {M N : MagmaCat} (f : M ⟶ N) : ofHom (Hom.hom f) = f
参数：f : M ⟶ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {M N : MagmaCat} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

@[to_additive (attr := simp)]
/-
**MagmaCat.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `MagmaCat`。
形式化陈述：ofHom_id {M : Type u} [Mul M] : ofHom (MulHom.id M) = 𝟙 (of M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {M : Type u} [Mul M] : ofHom (MulHom.id M) = 𝟙 (of M) := rfl

@[to_additive (attr := simp)]
/-
**MagmaCat.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `MagmaCat`。
形式化陈述：ofHom_comp {M N P : Type u} [Mul M] [Mul N] [Mul P] (f : M ->ₙ* N) (g : N 
->ₙ* P) : ofHom (g.comp f) = ofHom f ≫ ofHom g
参数：f : M ->ₙ* N；g : N ->ₙ* P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {M N P : Type u} [Mul M] [Mul N] [Mul P]
    (f : M →ₙ* N) (g : N →ₙ* P) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

@[to_additive]
/-
**MagmaCat.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `MagmaCat`。
形式化陈述：ofHom_apply {X Y : Type u} [Mul X] [Mul Y] (f : X ->ₙ* Y) (x : X) : (ofHom
 f) x = f x
参数：f : X ->ₙ* Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {X Y : Type u} [Mul X] [Mul Y] (f : X →ₙ* Y) (x : X) :
    (ofHom f) x = f x := rfl

@[to_additive]
/-
**MagmaCat.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `MagmaCat`。
形式化陈述：inv_hom_apply {M N : MagmaCat} (e : M ≅ N) (x : M) : e.inv (e.hom x) = x
参数：e : M ≅ N；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_hom_apply {M N : MagmaCat} (e : M ≅ N) (x : M) : e.inv (e.hom x) = x := by
  simp

@[to_additive]
/-
**MagmaCat.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `MagmaCat`。
形式化陈述：hom_inv_apply {M N : MagmaCat} (e : M ≅ N) (s : N) : e.hom (e.inv s) = s
参数：e : M ≅ N；s : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hom_inv_apply {M N : MagmaCat} (e : M ≅ N) (s : N) : e.hom (e.inv s) = s := by
  simp

@[to_additive (attr := simp)]
/-
**MagmaCat.mulEquiv_coe_eq** 是 Mathlib 中的一个引理，位于命名空间 `MagmaCat`。
形式化陈述：mulEquiv_coe_eq {X Y : Type _} [Mul X] [Mul Y] (e : X ≃* Y) : (ofHom (e : 
X ->ₙ* Y)).hom = ↑e
参数：e : X ≃* Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMulHomClass`：∀ {M : Type u_4} {N : Type u_5} (F : Type
 u_9) [inst : Mul M] [inst_1 : Mul N] [inst_2 : EquivLike F M N]   [h : MulEquiv
Class F M N], MulHo…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
lemma mulEquiv_coe_eq {X Y : Type _} [Mul X] [Mul Y] (e : X ≃* Y) :
    (ofHom (e : X →ₙ* Y)).hom = ↑e :=
  rfl

@[to_additive]
/-
**MagmaCat.** 是 Mathlib 中的一个实例，位于命名空间 `MagmaCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited MagmaCat :=
  ⟨MagmaCat.of PEmpty⟩

end MagmaCat

/-- The category of additive semigroups and semigroup morphisms. -/
/-
**AddSemigrp** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of additive semigroups and semigroup morphisms.
-/
structure AddSemigrp : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : AddSemigroup carrier]

/-- The category of semigroups and semigroup morphisms. -/
@[to_additive]
/-
**Semigrp** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of semigroups and semigroup morphisms.
-/
structure Semigrp : Type (u + 1) where
  /-- The underlying type. -/
  (carrier : Type u)
  [str : Semigroup carrier]

attribute [instance] AddSemigrp.str Semigrp.str

initialize_simps_projections AddSemigrp (carrier → coe, -str)
initialize_simps_projections Semigrp (carrier → coe, -str)

namespace Semigrp

@[to_additive]
/-
**Semigrp.** 是 Mathlib 中的一个实例，位于命名空间 `Semigrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort Semigrp (Type u) :=
  ⟨Semigrp.carrier⟩

attribute [coe] AddSemigrp.carrier Semigrp.carrier

/-- Construct a bundled `Semigrp` from the underlying type and typeclass. -/
@[to_additive /-- Construct a bundled `AddSemigrp` from the underlying type and typeclass. -/]
/-
**Semigrp.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `Semigrp`。
形式化陈述：of (M : Type u) [Semigroup M] : Semigrp
参数：M : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `Semigrp` from the underlying type and typeclass.
-/
abbrev of (M : Type u) [Semigroup M] : Semigrp := ⟨M⟩

end Semigrp

/-- The type of morphisms in `AddSemigrp R`. -/
@[ext]
/-
**AddSemigrp.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `AddSemigrp`。
形式化陈述：AddSemigrp → AddSemigrp → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `AddSemigrp R`.
-/
structure AddSemigrp.Hom (A B : AddSemigrp.{u}) where
  private mk ::
  /-- The underlying `AddHom`. -/
  hom' : A →ₙ+ B

/-- The type of morphisms in `Semigrp R`. -/
@[to_additive, ext]
/-
**Semigrp.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `Semigrp`。
形式化陈述：Semigrp → Semigrp → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `Semigrp R`.
-/
structure Semigrp.Hom (A B : Semigrp.{u}) where
  private mk ::
  /-- The underlying `MulHom`. -/
  hom' : A →ₙ* B

namespace Semigrp

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/-
**Semigrp.** 是 Mathlib 中的一个实例，位于命名空间 `Semigrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category Semigrp.{u} where
  Hom X Y := Hom X Y
  id X := ⟨MulHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
/-
**Semigrp.** 是 Mathlib 中的一个实例，位于命名空间 `Semigrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory Semigrp (· →ₙ* ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `Semigrp` back into a `MulHom`. -/
@[to_additive /-- Turn a morphism in `AddSemigrp` back into an `AddHom`. -/]
/-
**Semigrp.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `Semigrp.Hom`。
形式化陈述：{X Y : Semigrp} → X.Hom Y → ↑X →ₙ* ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `Semigrp` back into a `MulHom`.
-/
abbrev Hom.hom {X Y : Semigrp.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := Semigrp) f

/-- Typecheck a `MulHom` as a morphism in `Semigrp`. -/
@[to_additive /-- Typecheck an `AddHom` as a morphism in `AddSemigrp`. -/]
/-
**Semigrp.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `Semigrp`。
形式化陈述：ofHom {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X ->ₙ* Y) : of X ⟶ o
f Y
参数：f : X ->ₙ* Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `MulHom` as a morphism in `Semigrp`.
-/
abbrev ofHom {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := Semigrp) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**Semigrp.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `Semigrp.Hom.Simps`。
形式化陈述：(X Y : Semigrp) → X.Hom Y → ↑X →ₙ* ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (X Y : Semigrp.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)
initialize_simps_projections AddSemigrp.Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[to_additive (attr := simp)]
/-
**Semigrp.coe_id** 是 Mathlib 中的一个引理，位于命名空间 `Semigrp`。
形式化陈述：coe_id {X : Semigrp} : (𝟙 X : X -> X) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma coe_id {X : Semigrp} : (𝟙 X : X → X) = id := rfl

@[to_additive (attr := simp)]
/-
**Semigrp.coe_comp** 是 Mathlib 中的一个引理，位于命名空间 `Semigrp`。
形式化陈述：coe_comp {X Y Z : Semigrp} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g 
∘ f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comp {X Y Z : Semigrp} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[deprecated (since := "2026-02-10")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[to_additive (attr := ext)]
/-
**Semigrp.ext** 是 Mathlib 中的一个引理，位于命名空间 `Semigrp`。
形式化陈述：ext {X Y : Semigrp} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g
参数：w : forall x : X, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
-/
lemma ext {X Y : Semigrp} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[to_additive]
-- This is not `simp` to avoid rewriting in types of terms.
/-
**Semigrp.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `Semigrp`。
形式化陈述：coe_of (R : Type u) [Semigroup R] : ↑(Semigrp.of R) = R
参数：R : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (R : Type u) [Semigroup R] : ↑(Semigrp.of R) = R :=
  rfl

@[to_additive (attr := simp)]
/-
**Semigrp.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `Semigrp`。
形式化陈述：hom_id {X : Semigrp} : (𝟙 X : X ⟶ X).hom = MulHom.id X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_id {X : Semigrp} : (𝟙 X : X ⟶ X).hom = MulHom.id X := rfl

/- Provided for rewriting. -/
@[to_additive]
/-
**Semigrp.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `Semigrp`。
形式化陈述：id_apply (X : Semigrp) (x : X) : (𝟙 X : X ⟶ X) x = x
参数：X : Semigrp；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulHom.id_apply`：∀ (M : Type u_10) [inst : Mul M] (x : M), (MulHom.id M)
 x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (X : Semigrp) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[to_additive (attr := simp)]
/-
**Semigrp.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `Semigrp`。
形式化陈述：hom_comp {X Y T : Semigrp} (f : X ⟶ Y) (g : Y ⟶ T) : (f ≫ g).hom = g.hom.c
omp f.hom
参数：f : X ⟶ Y；g : Y ⟶ T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {X Y T : Semigrp} (f : X ⟶ Y) (g : Y ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
@[to_additive]
/-
**Semigrp.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `Semigrp`。
形式化陈述：comp_apply {X Y T : Semigrp} (f : X ⟶ Y) (g : Y ⟶ T) (x : X) : (f ≫ g) x =
 g (f x)
参数：f : X ⟶ Y；g : Y ⟶ T；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {X Y T : Semigrp} (f : X ⟶ Y) (g : Y ⟶ T) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[to_additive (attr := ext)]
/-
**Semigrp.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `Semigrp`。
形式化陈述：hom_ext {X Y : Semigrp} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Semigrp.Hom.ext`：∀ {A B : Semigrp} {x y : A.Hom B}, x.hom' = y.hom' → x 
= y
-/
lemma hom_ext {X Y : Semigrp} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[to_additive (attr := simp)]
/-
**Semigrp.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `Semigrp`。
形式化陈述：hom_ofHom {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X ->ₙ* Y) : (ofH
om f).hom = f
参数：f : X ->ₙ* Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y) : (ofHom f).hom = f := rfl

@[to_additive (attr := simp)]
/-
**Semigrp.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `Semigrp`。
形式化陈述：ofHom_hom {X Y : Semigrp} (f : X ⟶ Y) : ofHom (Hom.hom f) = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {X Y : Semigrp} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[to_additive (attr := simp)]
/-
**Semigrp.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `Semigrp`。
形式化陈述：ofHom_id {X : Type u} [Semigroup X] : ofHom (MulHom.id X) = 𝟙 (of X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {X : Type u} [Semigroup X] : ofHom (MulHom.id X) = 𝟙 (of X) := rfl

@[to_additive (attr := simp)]
/-
**Semigrp.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `Semigrp`。
形式化陈述：ofHom_comp {X Y Z : Type u} [Semigroup X] [Semigroup Y] [Semigroup Z] (f :
 X ->ₙ* Y) (g : Y ->ₙ* Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g
参数：f : X ->ₙ* Y；g : Y ->ₙ* Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {X Y Z : Type u} [Semigroup X] [Semigroup Y] [Semigroup Z]
    (f : X →ₙ* Y) (g : Y →ₙ* Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

@[to_additive]
/-
**Semigrp.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Semigrp`。
形式化陈述：ofHom_apply {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X ->ₙ* Y) (x :
 X) : (ofHom f) x = f x
参数：f : X ->ₙ* Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y) (x : X) :
    (ofHom f) x = f x := rfl

@[to_additive]
/-
**Semigrp.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Semigrp`。
形式化陈述：inv_hom_apply {X Y : Semigrp} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x
参数：e : X ≅ Y；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_hom_apply {X Y : Semigrp} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

@[to_additive]
/-
**Semigrp.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Semigrp`。
形式化陈述：hom_inv_apply {X Y : Semigrp} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s
参数：e : X ≅ Y；s : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hom_inv_apply {X Y : Semigrp} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

@[to_additive (attr := simp)]
/-
**Semigrp.mulEquiv_coe_eq** 是 Mathlib 中的一个引理，位于命名空间 `Semigrp`。
形式化陈述：mulEquiv_coe_eq {X Y : Type _} [Semigroup X] [Semigroup Y] (e : X ≃* Y) : 
(ofHom (e : X ->ₙ* Y)).hom = ↑e
参数：e : X ≃* Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMulHomClass`：∀ {M : Type u_4} {N : Type u_5} (F : Type
 u_9) [inst : Mul M] [inst_1 : Mul N] [inst_2 : EquivLike F M N]   [h : MulEquiv
Class F M N], MulHo…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
lemma mulEquiv_coe_eq {X Y : Type _} [Semigroup X] [Semigroup Y] (e : X ≃* Y) :
    (ofHom (e : X →ₙ* Y)).hom = ↑e :=
  rfl

@[to_additive]
/-
**Semigrp.** 是 Mathlib 中的一个实例，位于命名空间 `Semigrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited Semigrp :=
  ⟨Semigrp.of PEmpty⟩

@[to_additive]
/-
**Semigrp.hasForgetToMagmaCat** 是 Mathlib 中的一个实例，位于命名空间 `Semigrp`。
形式化陈述：hasForgetToMagmaCat : HasForget₂ Semigrp MagmaCat where forget₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToMagmaCat : HasForget₂ Semigrp MagmaCat where
  forget₂ :=
    { obj R := MagmaCat.of R
      map f := MagmaCat.ofHom f.hom }

end Semigrp

variable {X Y : Type u}

section

variable [Mul X] [Mul Y]

/-- Build an isomorphism in the category `MagmaCat` from a `MulEquiv` between `Mul`s. -/
@[to_additive (attr := simps)
      /-- Build an isomorphism in the category `AddMagmaCat` from an `AddEquiv` between `Add`s. -/]
/-
**MulEquiv.toMagmaCatIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulEquiv.toMagmaCatIso (e : X ≃* Y) : MagmaCat.of X ≅ MagmaCat.of Y where 
hom
参数：e : X ≃* Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MulEquiv.toMagmaCatIso (e : X ≃* Y) : MagmaCat.of X ≅ MagmaCat.of Y where
  hom := MagmaCat.ofHom e.toMulHom
  inv := MagmaCat.ofHom e.symm.toMulHom

end

section

variable [Semigroup X] [Semigroup Y]

/-- Build an isomorphism in the category `Semigroup` from a `MulEquiv` between `Semigroup`s. -/
@[to_additive (attr := simps)
  /-- Build an isomorphism in the category
  `AddSemigroup` from an `AddEquiv` between `AddSemigroup`s. -/]
/-
**MulEquiv.toSemigrpIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulEquiv.toSemigrpIso (e : X ≃* Y) : Semigrp.of X ≅ Semigrp.of Y where hom
参数：e : X ≃* Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MulEquiv.toSemigrpIso (e : X ≃* Y) : Semigrp.of X ≅ Semigrp.of Y where
  hom := Semigrp.ofHom e.toMulHom
  inv := Semigrp.ofHom e.symm.toMulHom

end

namespace CategoryTheory.Iso

/-- Build a `MulEquiv` from an isomorphism in the category `MagmaCat`. -/
@[to_additive
      /-- Build an `AddEquiv` from an isomorphism in the category `AddMagmaCat`. -/]
/-
**CategoryTheory.Iso.magmaCatIsoToMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Iso`。
形式化陈述：magmaCatIsoToMulEquiv {X Y : MagmaCat} (i : X ≅ Y) : X ≃* Y
参数：i : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def magmaCatIsoToMulEquiv {X Y : MagmaCat} (i : X ≅ Y) : X ≃* Y :=
  MulHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

/-- Build a `MulEquiv` from an isomorphism in the category `Semigroup`. -/
@[to_additive
  /-- Build an `AddEquiv` from an isomorphism in the category `AddSemigroup`. -/]
/-
**CategoryTheory.Iso.semigrpIsoToMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Iso`。
形式化陈述：semigrpIsoToMulEquiv {X Y : Semigrp} (i : X ≅ Y) : X ≃* Y
参数：i : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def semigrpIsoToMulEquiv {X Y : Semigrp} (i : X ≅ Y) : X ≃* Y :=
  MulHom.toMulEquiv i.hom.hom i.inv.hom (by ext; simp) (by ext; simp)

end CategoryTheory.Iso

/-- multiplicative equivalences between `Mul`s are the same as (isomorphic to) isomorphisms
in `MagmaCat` -/
@[to_additive
    /-- additive equivalences between `Add`s are the same
    as (isomorphic to) isomorphisms in `AddMagmaCat` -/]
/-
**mulEquivIsoMagmaIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mulEquivIsoMagmaIso {X Y : Type u} [Mul X] [Mul Y] : (X ≃* Y) ≅ (MagmaCat.
of X ≅ MagmaCat.of Y) where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulEquivIsoMagmaIso {X Y : Type u} [Mul X] [Mul Y] :
    (X ≃* Y) ≅ (MagmaCat.of X ≅ MagmaCat.of Y) where
  hom := ↾fun e ↦ e.toMagmaCatIso
  inv := ↾fun i ↦ i.magmaCatIsoToMulEquiv

/-- multiplicative equivalences between `Semigroup`s are the same as (isomorphic to) isomorphisms
in `Semigroup` -/
@[to_additive
  /-- additive equivalences between `AddSemigroup`s are
  the same as (isomorphic to) isomorphisms in `AddSemigroup` -/]
/-
**mulEquivIsoSemigrpIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mulEquivIsoSemigrpIso {X Y : Type u} [Semigroup X] [Semigroup Y] : (X ≃* Y
) ≅ (Semigrp.of X ≅ Semigrp.of Y) where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulEquivIsoSemigrpIso {X Y : Type u} [Semigroup X] [Semigroup Y] :
    (X ≃* Y) ≅ (Semigrp.of X ≅ Semigrp.of Y) where
  hom := ↾fun e ↦ e.toSemigrpIso
  inv := ↾fun i ↦ i.semigrpIsoToMulEquiv

@[to_additive]
/-
**MagmaCat.forgetReflectsIsos** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MagmaCat.forgetReflectsIsos : (forget MagmaCat.{u}).ReflectsIsomorphisms w
here reflects {X Y} f _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `MulHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : Mul M] [inst_
1 : Mul N] (self : M →ₙ* N) (x y : M),   self.toFun (x * y) = self.toFun x * sel
f.toF…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance MagmaCat.forgetReflectsIsos : (forget MagmaCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget MagmaCat).map f)
    let e : X ≃* Y := { f.hom, i.toEquiv with }
    exact e.toMagmaCatIso.isIso_hom

@[to_additive]
/-
**Semigrp.forgetReflectsIsos** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Semigrp.forgetReflectsIsos : (forget Semigrp.{u}).ReflectsIsomorphisms whe
re reflects {X Y} f _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `MulHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : Mul M] [inst_
1 : Mul N] (self : M →ₙ* N) (x y : M),   self.toFun (x * y) = self.toFun x * sel
f.toF…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance Semigrp.forgetReflectsIsos : (forget Semigrp.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget Semigrp).map f)
    let e : X ≃* Y := { f.hom, i.toEquiv with }
    exact e.toSemigrpIso.isIso_hom

/-- Ensure that `forget₂ CommMonCat MonCat` automatically reflects isomorphisms. -/
@[to_additive /-- Ensure that `forget₂ AddCommMonCat AddMonCat` automatically reflects
isomorphisms. -/]
/-
**Semigrp.forget** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Semigrp.forget₂_full : (forget₂ Semigrp MagmaCat).Full where
  map_surjective f := ⟨ofHom f.hom, rfl⟩

/-!
Once we've shown that the forgetful functors to type reflect isomorphisms,
we automatically obtain that the `forget₂` functors between our concrete categories
reflect isomorphisms.
-/

/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Once we've shown that the forgetful functors to type reflect isomorphisms,
we automatically obtain that the `forget₂` functors between our concrete categor
ies
reflect isomorphisms.
-/
example : (forget₂ Semigrp MagmaCat).ReflectsIsomorphisms := inferInstance
