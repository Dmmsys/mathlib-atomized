/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Kim Morrison
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.RepresentationTheory.Action
public import Mathlib.RepresentationTheory.Equiv

/-!
# `Rep k G` is the category of `k`-linear representations of `G`.

Given a `G`-representation `ρ` on a module `V`, you can construct the bundled representation as
`Rep.of ρ`. Conversely, given a bundled representation `A : Rep k G`, you can get the underlying
module as `A.V` and the representation on it as `A.ρ`.

-/

@[expose] public section

universe w w' u u' v v'

open CategoryTheory
open scoped MonoidAlgebra

/-- The category of representations of monoid `G` and their morphisms. -/
/-
**Rep** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(k : Type u) → (G : Type v) → [Semiring k] → [Monoid G] → Type (max (max u
 v) (w + 1))
参数：max u v；w + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of representations of monoid `G` and their morphisms.
-/
structure Rep (k : Type u) (G : Type v) [Semiring k] [Monoid G] where
  private mk ::
  /-- the underlying type of an object in `Rep k G` -/
  V : Type w
  [hV1 : AddCommGroup V]
  [hV2 : Module k V]
  /-- the underlying representation of an object in `Rep k G` -/
  ρ : Representation k G V

namespace Rep

noncomputable section

section semiring

variable {k : Type u} {G : Type v} [Semiring k] [Monoid G] {X Y : Type w} [AddCommGroup X]
  [AddCommGroup Y] [Module k X] [Module k Y] {ρ : Representation k G X} {σ : Representation k G Y}
  (A B C : Rep.{w} k G)

attribute [instance] hV1 hV2

initialize_simps_projections Rep (-hV1, -hV2)

/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (Rep k G) (Type w) := ⟨Rep.V⟩

attribute [coe] V

variable (ρ) in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The object in the category of representations associated to a type equipped a representation.
This is the preferred way to construct a term of `Rep k G`. -/
/-
**Rep.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：of : Rep.{w} k G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object in the category of representations associated to a type equipped a re
presentation.
This is the preferred way to construct a term of `Rep k G`.
-/
abbrev of : Rep.{w} k G := ⟨X, ρ⟩

variable (X ρ) in
/-
**Rep.of_V** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：of_V : (of ρ).V = X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_V : (of ρ).V = X := by with_reducible rfl

variable (X ρ) in
/-
**Rep.of_** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_ρ : (of ρ).ρ = ρ := by with_reducible rfl

/-- The type of morphisms in `Rep.{w} k G`. -/
@[ext]
/-
**Rep.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `Rep`。
形式化陈述：{k : Type u} → {G : Type v} → [inst : Semiring k] → [inst_1 : Monoid G] → 
Rep.{w, u, v} k G → Rep.{w, u, v} k G → Type w
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `Rep.{w} k G`.
-/
structure Hom where
  private mk ::
  /-- The underlying `G`-equivariant linear map. -/
  hom' : A.ρ.IntertwiningMap B.ρ

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (Rep.{w} k G) where
  Hom A B := Hom A B
  id A := ⟨.id A.ρ⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory (Rep.{w} k G) (fun A B ↦ A.ρ.IntertwiningMap B.ρ) where
  hom := Hom.hom'
  ofHom := Hom.mk

variable {A B} in
/-- Turn a morphism in `Rep` back into an `IntertwiningMap`. -/
/-
**Rep.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `Rep.Hom`。
形式化陈述：{k : Type u} →   {G : Type v} →     [inst : Semiring k] → [inst_1 : Monoid
 G] → {A B : Rep.{w, u, v} k G} → A.Hom B → A.ρ.IntertwiningMap B.ρ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `Rep` back into an `IntertwiningMap`.
-/
abbrev Hom.hom (f : Hom A B) := ConcreteCategory.hom (C := Rep k G) f

variable {A B} in
/-- Typecheck an `IntertwiningMap` as a morphism in `Rep`. -/
/-
**Rep.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：ofHom (f : ρ.IntertwiningMap σ) : of ρ ⟶ of σ
参数：f : ρ.IntertwiningMap σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck an `IntertwiningMap` as a morphism in `Rep`.
-/
abbrev ofHom (f : ρ.IntertwiningMap σ) : of ρ ⟶ of σ :=
  ConcreteCategory.ofHom (C := Rep.{w} k G) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**Rep.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `Rep.Hom.Simps`。
形式化陈述：{k : Type u} →   {G : Type v} →     [inst : Semiring k] → [inst_1 : Monoid
 G] → (A B : Rep.{w, u, v} k G) → A.Hom B → A.ρ.IntertwiningMap B.ρ
参数：A B : Rep.{w, u, v} k G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (f : Hom A B) := f.hom

initialize_simps_projections Hom (hom' → hom)

/-
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/
/-
**Rep.hom_id** 是 Mathlib 中的一个定理，位于命名空间 `Rep`。
形式化陈述：∀ {k : Type u} {G : Type v} [inst : Semiring k] [inst_1 : Monoid G] (A : R
ep.{w, u, v} k G),   Rep.Hom.hom (CategoryTheory.CategoryStruct.id A) = Represen
tation.IntertwiningMap.id A.ρ
参数：A : Rep.{w, u, v} k G；CategoryTheory.CategoryStruct.id A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
@[simp] lemma hom_id : (𝟙 A : A ⟶ A).hom = .id A.ρ := rfl

/- Provided for rewriting. -/
/-
**Rep.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：id_apply (a : A) : (𝟙 A : A ⟶ A) a = a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (a : A) : (𝟙 A : A ⟶ A) a = a := by
  simp [Representation.IntertwiningMap.id]
/-
**Rep.hom_comp** 是 Mathlib 中的一个定理，位于命名空间 `Rep`。
形式化陈述：∀ {k : Type u} {G : Type v} [inst : Semiring k] [inst_1 : Monoid G] (A B C
 : Rep.{w, u, v} k G) (f : A ⟶ B) (g : B ⟶ C),   Rep.Hom.hom (CategoryTheory.Cat
egoryStruct.comp f g) = (Rep.Hom.hom g).comp (Rep.Hom.hom f)
参数：A B C : Rep.{w, u, v} k G；f : A ⟶ B；g : B ⟶ C；CategoryTheory.CategoryStruct.c
omp f g；Rep.Hom.hom g；Rep.Hom.hom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
variable {A B C} in
/-
**Rep.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a)
参数：f : A ⟶ B；g : B ⟶ C；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp

variable {A B} in
/-
**Rep.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Rep`。
形式化陈述：∀ {k : Type u} {G : Type v} [inst : Semiring k] [inst_1 : Monoid G] {A B :
 Rep.{w, u, v} k G} {f g : A ⟶ B},   Rep.Hom.hom f = Rep.Hom.hom g → f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rep.Hom.ext`：∀ {k : Type u} {G : Type v} {inst : Semiring k} {inst_1 : M
onoid G} {A B : Rep.{w, u, v} k G} {x y : A.Hom B},   x.hom' = y.hom' → x = y
-/
@[ext] lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g := Hom.ext hf

variable {A B} in
/-
**Rep.hom_comm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：hom_comm_apply (f : A ⟶ B) (g : G) (a : A) : f.hom (A.ρ g a) = B.ρ g (f.ho
m a)
参数：f : A ⟶ B；g : G；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Representation.IntertwiningMap.isIntertwining'`：∀ {A : Type u_1} {G : Ty
pe u_2} {V : Type u_3} {W : Type u_4} [inst : Semiring A] [inst_1 : Monoid G]   
[inst_2 : AddCommMonoid V] [inst_3 :…
-/
lemma hom_comm_apply (f : A ⟶ B) (g : G) (a : A) : f.hom (A.ρ g a) = B.ρ g (f.hom a) := by
  simpa using congr($(f.hom.2 g) a)

variable {Z : Type w} [AddCommGroup Z] [Module k Z] {τ : Representation k G Z}
/-
**Rep.hom_ofHom** 是 Mathlib 中的一个定理，位于命名空间 `Rep`。
形式化陈述：∀ {k : Type u} {G : Type v} [inst : Semiring k] [inst_1 : Monoid G] {X Y :
 Type w} [inst_2 : AddCommGroup X]   [inst_3 : AddCommGroup Y] [inst_4 : _root_.
Module k X] [inst_5 : _root_.Module k Y] {ρ : Representation k G X}   {σ : Repre
sentation k G Y} (f : ρ.IntertwiningMap σ), Rep.Hom.hom (Rep.ofHom f) = f
参数：f : ρ.IntertwiningMap σ；Rep.ofHom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_ofHom (f : ρ.IntertwiningMap σ) : (ofHom f).hom = f := rfl
/-
**Rep.ofHom_hom** 是 Mathlib 中的一个定理，位于命名空间 `Rep`。
形式化陈述：∀ {k : Type u} {G : Type v} [inst : Semiring k] [inst_1 : Monoid G] (A B :
 Rep.{w, u, v} k G) (f : A ⟶ B),   Rep.ofHom (Rep.Hom.hom f) = f
参数：A B : Rep.{w, u, v} k G；f : A ⟶ B；Rep.Hom.hom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofHom_hom (f : A ⟶ B) : ofHom f.hom = f := rfl
/-
**Rep.ofHom_id** 是 Mathlib 中的一个定理，位于命名空间 `Rep`。
形式化陈述：∀ {k : Type u} {G : Type v} [inst : Semiring k] [inst_1 : Monoid G] {Y : T
ype w} [inst_2 : AddCommGroup Y]   [inst_3 : _root_.Module k Y] {σ : Representat
ion k G Y},   Rep.ofHom (Representation.IntertwiningMap.id σ) = CategoryTheory.C
ategoryStruct.id (Rep.of σ)
参数：Representation.IntertwiningMap.id σ；Rep.of σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofHom_id : ofHom (.id σ) = 𝟙 (of σ) := rfl

@[simp]
/-
**Rep.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：ofHom_comp (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) : ofHom (g.
comp f) = ofHom f ≫ ofHom g
参数：f : ρ.IntertwiningMap σ；g : σ.IntertwiningMap τ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) :
  ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl
/-
**Rep.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：ofHom_apply (f : ρ.IntertwiningMap σ) (x : X) : ofHom f x = f x
参数：f : ρ.IntertwiningMap σ；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply (f : ρ.IntertwiningMap σ) (x : X) : ofHom f x = f x := rfl
/-
**Rep.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：inv_hom_apply (e : A ≅ B) (x : A) : e.inv.hom (e.hom.hom x) = x
参数：e : A ≅ B；x : A。
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
lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv.hom (e.hom.hom x) = x := by simp
/-
**Rep.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：hom_inv_apply (e : A ≅ B) (x : B) : e.hom.hom (e.inv.hom x) = x
参数：e : A ≅ B；x : B。
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
lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom.hom (e.inv.hom x) = x := by simp
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Rep.{u} k G) := ⟨of (Representation.trivial k G PUnit)⟩
/-
**Rep.forget_obj** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：forget_obj : (forget (Rep.{w} k G)).obj A = A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_obj : (forget (Rep.{w} k G)).obj A = A := rfl
/-
**Rep.forget_map** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：forget_map (f : A ⟶ B) : (forget (Rep.{w} k G)).map f = (f : _ -> _)
参数：f : A ⟶ B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_map (f : A ⟶ B) : (forget (Rep.{w} k G)).map f = (f : _ → _) := rfl

/-- An equiv between the underlying representations induce isomorphism between objects in
  `Rep k G`. -/
@[simps]
/-
**Rep.mkIso** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：mkIso (e : ρ.Equiv σ) : of ρ ≅ of σ where hom
参数：e : ρ.Equiv σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equiv between the underlying representations induce isomorphism between objec
ts in
  `Rep k G`.
-/
def mkIso (e : ρ.Equiv σ) : of ρ ≅ of σ where
  hom := ofHom e.toIntertwiningMap
  inv := ofHom e.symm.toIntertwiningMap

@[simp]
/-
**Rep.mkIso_hom_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：mkIso_hom_hom_apply (e : ρ.Equiv σ) (x : X) : (mkIso e).hom.hom x = e.toLi
nearMap x
参数：e : ρ.Equiv σ；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkIso_hom_hom_apply (e : ρ.Equiv σ) (x : X) :
    (mkIso e).hom.hom x = e.toLinearMap x := rfl

@[simp]
/-
**Rep.mkIso_hom_hom_toLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：mkIso_hom_hom_toLinearMap (e : ρ.Equiv σ) : (mkIso e).hom.hom.toLinearMap 
= e.toLinearMap
参数：e : ρ.Equiv σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkIso_hom_hom_toLinearMap (e : ρ.Equiv σ) :
    (mkIso e).hom.hom.toLinearMap = e.toLinearMap := rfl

@[simp]
/-
**Rep.mkIso_inv_hom_toLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：mkIso_inv_hom_toLinearMap (e : ρ.Equiv σ) : (mkIso e).inv.hom.toLinearMap 
= e.symm.toIntertwiningMap.toLinearMap
参数：e : ρ.Equiv σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkIso_inv_hom_toLinearMap (e : ρ.Equiv σ) :
    (mkIso e).inv.hom.toLinearMap = e.symm.toIntertwiningMap.toLinearMap := rfl

@[simp]
/-
**Rep.mkIso_inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：mkIso_inv_hom_apply (e : ρ.Equiv σ) (y : Y) : (mkIso e).inv.hom y = e.symm
 y
参数：e : ρ.Equiv σ；y : Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkIso_inv_hom_apply (e : ρ.Equiv σ) (y : Y) :
    (mkIso e).inv.hom y = e.symm y := rfl

@[simp]
/-
**Rep.mkIso_hom_hom** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：mkIso_hom_hom (e : ρ.Equiv σ) : (mkIso e).hom.hom = e.toIntertwiningMap
参数：e : ρ.Equiv σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkIso_hom_hom (e : ρ.Equiv σ) :
    (mkIso e).hom.hom = e.toIntertwiningMap := rfl

variable {A B C}

/-- The equivalence between representations induced from iso between objects in `Rep k G`. -/
@[simps]
/-
**Rep._root_.Representation.equivOfIso** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between representations induced from iso between objects in `Rep
 k G`.
-/
def _root_.Representation.equivOfIso (i : A ≅ B) : A.ρ.Equiv B.ρ where
  __ := i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp
/-
**Rep.reflectsIsomorphisms_forget** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
形式化陈述：reflectsIsomorphisms_forget : (forget (Rep.{w} k G)).ReflectsIsomorphisms 
where reflects {X Y} f _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance reflectsIsomorphisms_forget : (forget (Rep.{w} k G)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (Rep.{w} k G)).map f)
    let e : X.ρ.Equiv Y.ρ := { f.hom, i.toEquiv with }
    exact (mkIso e).isIso_hom
/-
**Rep.hom_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：hom_bijective : Function.Bijective (Rep.Hom.hom : (A ⟶ B) -> (A.ρ.Intertwi
ningMap B.ρ)) where left _ _ h
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rep.hom_ext`：∀ {k : Type u} {G : Type v} [inst : Semiring k] [inst_1 : M
onoid G] {A B : Rep.{w, u, v} k G} {f g : A ⟶ B},   Rep.Hom.hom f = Rep.Hom.hom 
g…
· 使用定理 `Rep.hom_ofHom`：∀ {k : Type u} {G : Type v} [inst : Semiring k] [inst_1 :
 Monoid G] {X Y : Type w} [inst_2 : AddCommGroup X]   [inst_3 : AddCommGroup Y] 
[in…
-/
lemma hom_bijective :
    Function.Bijective (Rep.Hom.hom : (A ⟶ B) → (A.ρ.IntertwiningMap B.ρ)) where
  left _ _ h := Rep.hom_ext h
  right f := ⟨Rep.ofHom f, Rep.hom_ofHom f⟩

/-- Convenience shortcut for `Rep.hom_bijective.injective`. -/
/-
**Rep.hom_injective** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：hom_injective : Function.Injective (Hom.hom : (A ⟶ B) -> (A.ρ.Intertwining
Map B.ρ))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用引理 `Rep.hom_bijective`：hom_bijective : Function.Bijective (Rep.Hom.hom : (A 
⟶ B) -> (A.ρ.IntertwiningMap B.ρ)) where left _ _ h

--- 原说明 ---
Convenience shortcut for `Rep.hom_bijective.injective`.
-/
lemma hom_injective :
    Function.Injective (Hom.hom : (A ⟶ B) → (A.ρ.IntertwiningMap B.ρ)) :=
  hom_bijective.injective

/-- Convenience shortcut for `Rep.hom_bijective.surjective`. -/
/-
**Rep.hom_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：hom_surjective : Function.Surjective (Hom.hom : (A ⟶ B) -> (A.ρ.Intertwini
ngMap B.ρ))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用引理 `Rep.hom_bijective`：hom_bijective : Function.Bijective (Rep.Hom.hom : (A 
⟶ B) -> (A.ρ.IntertwiningMap B.ρ)) where left _ _ h

--- 原说明 ---
Convenience shortcut for `Rep.hom_bijective.surjective`.
-/
lemma hom_surjective :
    Function.Surjective (Hom.hom : (A ⟶ B) → (A.ρ.IntertwiningMap B.ρ)) :=
  hom_bijective.surjective

/-- The morphisms between two objects in `Rep k G` has an equivalence to the intertwining maps
  between their underlying representations. -/
@[simps]
/-
**Rep.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：homEquiv : (A ⟶ B) ≃ (A.ρ.IntertwiningMap B.ρ) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphisms between two objects in `Rep k G` has an equivalence to the intertw
ining maps
  between their underlying representations.
-/
def homEquiv : (A ⟶ B) ≃ (A.ρ.IntertwiningMap B.ρ) where
  toFun := Hom.hom
  invFun := ofHom
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (A ⟶ B) where add f g := ofHom (f.hom + g.hom)
/-
**Rep.ofHom_add** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：ofHom_add (f g : ρ.IntertwiningMap σ) : ofHom (f + g) = ofHom f + ofHom g
参数：f g : ρ.IntertwiningMap σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_add (f g : ρ.IntertwiningMap σ) :
    ofHom (f + g) = ofHom f + ofHom g := rfl
/-
**Rep.add_hom** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：add_hom (f g : A ⟶ B) : (f + g).hom = f.hom + g.hom
参数：f g : A ⟶ B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma add_hom (f g : A ⟶ B) : (f + g).hom = f.hom + g.hom := rfl
/-
**Rep.hom_comp_toLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：hom_comp_toLinearMap (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom.toLinearMap = g
.hom.toLinearMap ∘ₗ f.hom.toLinearMap
参数：f : A ⟶ B；g : B ⟶ C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp_toLinearMap (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom.toLinearMap = g.hom.toLinearMap ∘ₗ f.hom.toLinearMap := rfl
/-
**Rep.add_comp** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：add_comp (f₁ f₂ : A ⟶ B) (g : B ⟶ C) : (f₁ + f₂) ≫ g = f₁ ≫ g + f₂ ≫ g
参数：f₁ f₂ : A ⟶ B；g : B ⟶ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rep.hom_ext`：∀ {k : Type u} {G : Type v} [inst : Semiring k] [inst_1 : M
onoid G] {A B : Rep.{w, u, v} k G} {f g : A ⟶ B},   Rep.Hom.hom f = Rep.Hom.hom 
g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Representation.IntertwiningMap.add_comp`：add_comp (f : IntertwiningMap σ
 τ) (g₁ g₂ : IntertwiningMap ρ σ) : comp f (g₁ + g₂) = comp f g₁ + comp f g₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add_comp (f₁ f₂ : A ⟶ B) (g : B ⟶ C) :
    (f₁ + f₂) ≫ g = f₁ ≫ g + f₂ ≫ g := by
  ext1
  simp [add_hom, Representation.IntertwiningMap.add_comp]
/-
**Rep.comp_add** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：comp_add (f : A ⟶ B) (g₁ g₂ : B ⟶ C) : f ≫ (g₁ + g₂) = f ≫ g₁ + f ≫ g₂
参数：f : A ⟶ B；g₁ g₂ : B ⟶ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rep.hom_ext`：∀ {k : Type u} {G : Type v} [inst : Semiring k] [inst_1 : M
onoid G] {A B : Rep.{w, u, v} k G} {f g : A ⟶ B},   Rep.Hom.hom f = Rep.Hom.hom 
g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Representation.IntertwiningMap.comp_add`：comp_add (f₁ f₂ : IntertwiningM
ap σ τ) (g : IntertwiningMap ρ σ) : (f₁ + f₂).comp g = comp f₁ g + comp f₂ g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_add (f : A ⟶ B) (g₁ g₂ : B ⟶ C) :
    f ≫ (g₁ + g₂) = f ≫ g₁ + f ≫ g₂ := by
  ext1
  simp [add_hom, Representation.IntertwiningMap.comp_add]
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (A ⟶ B) where
  zero := ofHom (0 : A.ρ.IntertwiningMap B.ρ)

@[simp]
/-
**Rep.ofHom_zero** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：ofHom_zero : ofHom (0 : ρ.IntertwiningMap σ) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_zero : ofHom (0 : ρ.IntertwiningMap σ) = 0 := rfl

@[simp]
/-
**Rep.zero_hom** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：zero_hom : (0 : A ⟶ B).hom = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zero_hom : (0 : A ⟶ B).hom = 0 := rfl
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℕ (A ⟶ B) where smul n f := ofHom (n • f.hom)
/-
**Rep.ofHom_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：ofHom_nsmul (f : ρ.IntertwiningMap σ) (n : Nat) : ofHom (n • f) = n • ofHo
m f
参数：f : ρ.IntertwiningMap σ；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_nsmul (f : ρ.IntertwiningMap σ) (n : ℕ) :
    ofHom (n • f) = n • ofHom f := rfl
/-
**Rep.nsmul_hom** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：nsmul_hom (f : A ⟶ B) (n : Nat) : (n • f).hom = n • f.hom
参数：f : A ⟶ B；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nsmul_hom (f : A ⟶ B) (n : ℕ) : (n • f).hom = n • f.hom := rfl
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (A ⟶ B) where neg f := ofHom (-f.hom)
/-
**Rep.ofHom_neg** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：ofHom_neg (f : ρ.IntertwiningMap σ) : ofHom (-f) = -ofHom f
参数：f : ρ.IntertwiningMap σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_neg (f : ρ.IntertwiningMap σ) : ofHom (-f) = -ofHom f := rfl
/-
**Rep.neg_hom** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：neg_hom (f : A ⟶ B) : (-f).hom = -f.hom
参数：f : A ⟶ B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma neg_hom (f : A ⟶ B) : (-f).hom = -f.hom := rfl
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (A ⟶ B) where sub f g := ofHom (f.hom - g.hom)
/-
**Rep.ofHom_sub** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：ofHom_sub (f g : ρ.IntertwiningMap σ) : ofHom (f - g) = ofHom f - ofHom g
参数：f g : ρ.IntertwiningMap σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_sub (f g : ρ.IntertwiningMap σ) : ofHom (f - g) = ofHom f - ofHom g := rfl
/-
**Rep.sub_hom** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：sub_hom (f g : A ⟶ B) : (f - g).hom = f.hom - g.hom
参数：f g : A ⟶ B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sub_hom (f g : A ⟶ B) : (f - g).hom = f.hom - g.hom := rfl
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℤ (A ⟶ B) where smul n f := ofHom (n • f.hom)
/-
**Rep.ofHom_zsmul** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：ofHom_zsmul (f : ρ.IntertwiningMap σ) (n : Int) : ofHom (n • f) = n • ofHo
m f
参数：f : ρ.IntertwiningMap σ；n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_zsmul (f : ρ.IntertwiningMap σ) (n : ℤ) : ofHom (n • f) = n • ofHom f := rfl
/-
**Rep.zsmul_hom** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：zsmul_hom (f : A ⟶ B) (n : Int) : (n • f).hom = n • f.hom
参数：f : A ⟶ B；n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zsmul_hom (f : A ⟶ B) (n : ℤ) : (n • f).hom = n • f.hom := rfl
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (A ⟶ B) := fast_instance% hom_injective.addCommGroup
    Rep.Hom.hom zero_hom add_hom neg_hom sub_hom nsmul_hom zsmul_hom
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preadditive (Rep.{w} k G) where
  add_comp _ _ _ := add_comp
  comp_add _ _ _ := comp_add
/-
**Rep.sum_hom** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：sum_hom {ι : Type u'} (f : ι -> (A ⟶ B)) (s : Finset ι) : (∑ i in s, f i).
hom = ∑ i in s, (f i).hom
参数：f : ι -> (A ⟶ B)；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
-/
lemma sum_hom {ι : Type u'} (f : ι → (A ⟶ B)) (s : Finset ι) :
    (∑ i ∈ s, f i).hom = ∑ i ∈ s, (f i).hom := by
  classical induction s using Finset.induction with
  | empty => simp
  | insert a s ha h => simp [Finset.sum_insert ha, add_hom, h]
/-
**Rep.ofHom_sum** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：ofHom_sum {ι : Type u'} {M N : Type v'} [AddCommGroup M] [AddCommGroup N] 
[Module k M] [Module k N] {σ : Representation k G M} {ρ : Representation k G N} 
(f : ι -> σ.IntertwiningMap ρ) (s : Finset ι) : ofHom (∑ i in s, f i) = ∑ i in s
, ofHom (f i)
参数：f : ι -> σ.IntertwiningMap ρ；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
-/
lemma ofHom_sum {ι : Type u'} {M N : Type v'} [AddCommGroup M] [AddCommGroup N] [Module k M]
    [Module k N] {σ : Representation k G M} {ρ : Representation k G N} (f : ι → σ.IntertwiningMap ρ)
    (s : Finset ι) :
    ofHom (∑ i ∈ s, f i) = ∑ i ∈ s, ofHom (f i) := by
  classical induction s using Finset.induction with
  | empty => simp
  | insert a s ha h => simp [Finset.sum_insert ha, ofHom_add, h]

variable (k G) in
/-- The trivial `k`-linear `G`-representation on a `k`-module `V.` -/
/-
**Rep.trivial** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：trivial (V : Type w) [AddCommGroup V] [Module k V] : Rep k G
参数：V : Type w。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial `k`-linear `G`-representation on a `k`-module `V.`
-/
abbrev trivial (V : Type w) [AddCommGroup V] [Module k V] : Rep k G :=
  Rep.of (Representation.trivial k G V)
/-
**Rep.trivial_V** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：trivial_V {V : Type w} [AddCommGroup V] [Module k V] : (trivial k G V).V =
 V
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma trivial_V {V : Type w} [AddCommGroup V] [Module k V] : (trivial k G V).V = V := rfl
/-
**Rep.trivial_** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma trivial_ρ {V : Type w} [AddCommGroup V] [Module k V] (g : G) :
    (trivial k G V).ρ g = LinearMap.id := rfl

@[simp]
/-
**Rep.trivial_** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma trivial_ρ_apply {V : Type w} [AddCommGroup V] [Module k V] (g : G) (v : V) :
    (trivial k G V).ρ g v = v := rfl
/-
**Rep.** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ρ_mul (g1 g2 : G) : A.ρ (g1 * g2) = A.ρ g1 ∘ₗ A.ρ g2 := by ext; simp

section Commutative

variable {G : Type v} [CommMonoid G]
variable (A : Rep k G)

/-- Given a representation `A` of a commutative monoid `G`, the map `ρ_A(g)` is a representation
morphism `A ⟶ A` for any `g : G`. -/
/-
**Rep.applyAsHom** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：applyAsHom (g : G) : A ⟶ A
参数：g : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a representation `A` of a commutative monoid `G`, the map `ρ_A(g)` is a re
presentation
morphism `A ⟶ A` for any `g : G`.
-/
def applyAsHom (g : G) : A ⟶ A := Rep.ofHom ⟨A.ρ g, by simp [← ρ_mul, mul_comm]⟩

@[simp]
/-
**Rep.applyAsHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：applyAsHom_apply {A : Rep k G} (g : G) (x : A) : (A.applyAsHom g).hom x = 
A.ρ g x
参数：g : G；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma applyAsHom_apply {A : Rep k G} (g : G) (x : A) : (A.applyAsHom g).hom x = A.ρ g x := rfl

@[reassoc, elementwise]
/-
**Rep.applyAsHom_comm** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：applyAsHom_comm {A B : Rep k G} (f : A ⟶ B) (g : G) : A.applyAsHom g ≫ f =
 f ≫ B.applyAsHom g
参数：f : A ⟶ B；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rep.hom_ext`：∀ {k : Type u} {G : Type v} [inst : Semiring k] [inst_1 : M
onoid G] {A B : Rep.{w, u, v} k G} {f g : A ⟶ B},   Rep.Hom.hom f = Rep.Hom.hom 
g…
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rep.hom_comm_apply`：hom_comm_apply (f : A ⟶ B) (g : G) (a : A) : f.hom (
A.ρ g a) = B.ρ g (f.hom a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma applyAsHom_comm {A B : Rep k G} (f : A ⟶ B) (g : G) :
    A.applyAsHom g ≫ f = f ≫ B.applyAsHom g := by
  ext; simp [hom_comm_apply]

end Commutative

end semiring

section ring

variable {k : Type u} {G : Type v} [Ring k] [Monoid G]

section setup

variable (k G)

/-- Given a `G`-action on `H`, this is `k[H]` bundled with the natural representation
`G →* End(k[H])` as a term of type `Rep k G`. -/
/-
**Rep.ofMulAction** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：ofMulAction (H : Type w') [MulAction G H] : Rep k G
参数：H : Type w'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `G`-action on `H`, this is `k[H]` bundled with the natural representatio
n
`G →* End(k[H])` as a term of type `Rep k G`.
-/
abbrev ofMulAction (H : Type w') [MulAction G H] : Rep k G :=
  of <| Representation.ofMulAction k G H

/-- The `k`-linear `G`-representation on `k[G]`, induced by left multiplication. -/
/-
**Rep.leftRegular** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：leftRegular : Rep k G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `k`-linear `G`-representation on `k[G]`, induced by left multiplication.
-/
abbrev leftRegular : Rep k G :=
  ofMulAction k G G

/-- The `k`-linear `G`-representation on `k[Gⁿ]`, induced by left multiplication. -/
/-
**Rep.diagonal** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：diagonal (n : Nat) : Rep k G
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `k`-linear `G`-representation on `k[Gⁿ]`, induced by left multiplication.
-/
abbrev diagonal (n : ℕ) : Rep k G :=
  ofMulAction k G (Fin n → G)

/-- The natural isomorphism between the representations on `k[G¹]` and `k[G]` induced by left
multiplication in `G`. -/
/-
**Rep.diagonalOneIsoLeftRegular** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：diagonalOneIsoLeftRegular : diagonal k G 1 ≅ leftRegular k G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism between the representations on `k[G¹]` and `k[G]` induce
d by left
multiplication in `G`.
-/
abbrev diagonalOneIsoLeftRegular :
    diagonal k G 1 ≅ leftRegular k G := Rep.mkIso (Representation.diagonalOneEquivLeftRegular k G)

/-- When `H = {1}`, the `G`-representation on `k[H]` induced by an action of `G` on `H` is
isomorphic to the trivial representation on `k`. -/
/-
**Rep.ofMulActionSubsingletonIsoTrivial** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：ofMulActionSubsingletonIsoTrivial (H : Type u) [Subsingleton H] [MulOneCla
ss H] [MulAction G H] : ofMulAction k G H ≅ trivial k G k
参数：H : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `H = {1}`, the `G`-representation on `k[H]` induced by an action of `G` on 
`H` is
isomorphic to the trivial representation on `k`.
-/
abbrev ofMulActionSubsingletonIsoTrivial
    (H : Type u) [Subsingleton H] [MulOneClass H] [MulAction G H] :
    ofMulAction k G H ≅ trivial k G k :=
  mkIso <| Representation.ofMulActionSubsingletonEquivTrivial k G H

section

variable (A : Type w') [AddCommGroup A] [Module k A] [DistribMulAction G A] [SMulCommClass G k A]

/-- Turns a `k`-module `A` with a compatible `DistribMulAction` of a monoid `G` into a
`k`-linear `G`-representation on `A`. -/
/-
**Rep.ofDistribMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：ofDistribMulAction : Rep k G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turns a `k`-module `A` with a compatible `DistribMulAction` of a monoid `G` into
 a
`k`-linear `G`-representation on `A`.
-/
def ofDistribMulAction : Rep k G := Rep.of (Representation.ofDistribMulAction k G A)
/-
**Rep.ofDistribMulAction_** 是 Mathlib 中的一个定理，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ofDistribMulAction_ρ_apply_apply (g : G) (a : A) :
    (ofDistribMulAction k G A).ρ g a = g • a := rfl

/-- Given an `R`-algebra `S`, the `ℤ`-linear representation associated to the natural action of
`S ≃ₐ[R] S` on `S`. -/
/-
**Rep.ofAlgebraAut** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：(R : Type u_1) →   (S : Type u_2) →     [inst : CommRing R] → [inst_1 : Co
mmRing S] → [inst_2 : Algebra R S] → Rep.{u_2, 0, u_2} ℤ (S ≃ₐ[R] S)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an `R`-algebra `S`, the `ℤ`-linear representation associated to the natura
l action of
`S ≃ₐ[R] S` on `S`.
-/
@[simp] def ofAlgebraAut (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    Rep ℤ (S ≃ₐ[R] S) := ofDistribMulAction ℤ (S ≃ₐ[R] S) S

end

section
variable (M G : Type*) [Monoid M] [CommGroup G] [MulDistribMulAction M G]

/-- Turns a `CommGroup` `G` with a `MulDistribMulAction` of a monoid `M` into a
`ℤ`-linear `M`-representation on `Additive G`. -/
/-
**Rep.ofMulDistribMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：ofMulDistribMulAction : Rep Int M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turns a `CommGroup` `G` with a `MulDistribMulAction` of a monoid `M` into a
`ℤ`-linear `M`-representation on `Additive G`.
-/
def ofMulDistribMulAction : Rep ℤ M := Rep.of (Representation.ofMulDistribMulAction M G)

variable {G M}

/-- Unfolds `ofMulDistribMulAction`; useful to keep track of additivity. -/
@[simps!]
/-
**Rep.toAdditive** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：toAdditive : ofMulDistribMulAction M G ≃+ Additive G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Unfolds `ofMulDistribMulAction`; useful to keep track of additivity.
-/
def toAdditive : ofMulDistribMulAction M G ≃+ Additive G := AddEquiv.refl _
/-
**Rep.ofMulDistribMulAction_** 是 Mathlib 中的一个定理，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ofMulDistribMulAction_ρ_apply_apply (g : M) (a : Additive G) :
    (ofMulDistribMulAction M G).ρ g a = Additive.ofMul (g • a.toMul) := rfl

/-- Given an `R`-algebra `S`, the `ℤ`-linear representation associated to the natural action of
`S ≃ₐ[R] S` on `Sˣ`. -/
/-
**Rep.ofAlgebraAutOnUnits** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：(R : Type u_3) →   (S : Type u_4) →     [inst : CommRing R] → [inst_1 : Co
mmRing S] → [inst_2 : Algebra R S] → Rep.{u_4, 0, u_4} ℤ (S ≃ₐ[R] S)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an `R`-algebra `S`, the `ℤ`-linear representation associated to the natura
l action of
`S ≃ₐ[R] S` on `Sˣ`.
-/
@[simp] def ofAlgebraAutOnUnits (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    Rep ℤ (S ≃ₐ[R] S) := Rep.ofMulDistribMulAction (S ≃ₐ[R] S) Sˣ

end

variable {k G}

/-- Given an element `x : A`, there is a natural morphism of representations `k[G] ⟶ A` sending
`g ↦ A.ρ(g)(x).` -/
/-
**Rep.leftRegularHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：leftRegularHom (A : Rep k G) (x : A) : leftRegular k G ⟶ A
参数：A : Rep k G；x : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an element `x : A`, there is a natural morphism of representations `k[G] ⟶
 A` sending
`g ↦ A.ρ(g)(x).`
-/
abbrev leftRegularHom (A : Rep k G) (x : A) : leftRegular k G ⟶ A :=
  Rep.ofHom ⟨Finsupp.lift A k G (fun g ↦ A.ρ g x) ∘ₗ (MonoidAlgebra.coeffLinearEquiv _).toLinearMap,
    fun g ↦ by ext; simp⟩
/-
**Rep.leftRegularHom_hom_single** 是 Mathlib 中的一个定理，位于命名空间 `Rep`。
形式化陈述：leftRegularHom_hom_single {A : Rep k G} (g : G) (x : A) (r : k) : (leftReg
ularHom A x).hom (.single g r) = r • A.ρ g x
参数：g : G；x : A；r : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_apply`：∀ (R : Type u_1) {S : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Module R
 S]   (a : MonoidAlgebra S…
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftRegularHom_hom_single {A : Rep k G} (g : G) (x : A) (r : k) :
    (leftRegularHom A x).hom (.single g r) = r • A.ρ g x := by
  simp [leftRegularHom]

variable (A : Rep k G)

/-- Given a `k`-linear `G`-representation `(V, ρ)`, this is the representation defined by
restricting `ρ` to a `G`-invariant `k`-submodule of `V`. -/
/-
**Rep.subrepresentation** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：subrepresentation (W : Submodule k A) (le_comap : forall g, W <= W.comap (
A.ρ g)) : Rep k G
参数：W : Submodule k A；le_comap : forall g, W <= W.comap (A.ρ g)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `k`-linear `G`-representation `(V, ρ)`, this is the representation defin
ed by
restricting `ρ` to a `G`-invariant `k`-submodule of `V`.
-/
abbrev subrepresentation (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    Rep k G := Rep.of (A.ρ.subrepresentation W le_comap)

/-- The natural inclusion of a subrepresentation into the ambient representation. -/
@[simps!]
/-
**Rep.subtype** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：subtype (W : Submodule k A) (le_comap : forall g, W <= W.comap (A.ρ g)) : 
subrepresentation A W le_comap ⟶ A
参数：W : Submodule k A；le_comap : forall g, W <= W.comap (A.ρ g)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural inclusion of a subrepresentation into the ambient representation.
-/
def subtype (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    subrepresentation A W le_comap ⟶ A := Rep.ofHom ⟨W.subtype, fun _ ↦ rfl⟩

/-- Given a `k`-linear `G`-representation `(V, ρ)` and a `G`-invariant `k`-submodule `W ≤ V`, this
is the representation induced on `V ⧸ W` by `ρ`. -/
/-
**Rep.quotient** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：quotient (W : Submodule k A) (le_comap : forall g, W <= W.comap (A.ρ g)) :
 Rep k G
参数：W : Submodule k A；le_comap : forall g, W <= W.comap (A.ρ g)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `k`-linear `G`-representation `(V, ρ)` and a `G`-invariant `k`-submodule
 `W ≤ V`, this
is the representation induced on `V ⧸ W` by `ρ`.
-/
abbrev quotient (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    Rep k G := Rep.of (A.ρ.quotient W le_comap)

/-- The natural projection from a representation to its quotient by a subrepresentation. -/
@[simps!]
/-
**Rep.mkQ** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：mkQ (W : Submodule k A) (le_comap : forall g, W <= W.comap (A.ρ g)) : A ⟶ 
quotient A W le_comap
参数：W : Submodule k A；le_comap : forall g, W <= W.comap (A.ρ g)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural projection from a representation to its quotient by a subrepresentat
ion.
-/
def mkQ (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    A ⟶ quotient A W le_comap := Rep.ofHom ⟨W.mkQ, fun _ ↦ rfl⟩

end setup

variable (k G) in
/-- The functor equipping a module with the trivial representation. -/
@[implicit_reducible, simps! obj_V map_hom]
/-
**Rep.trivialFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：trivialFunctor : ModuleCat.{w} k ⥤ Rep.{w} k G where obj V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor equipping a module with the trivial representation.
-/
def trivialFunctor : ModuleCat.{w} k ⥤ Rep.{w} k G where
  obj V := trivial k G V
  map f := ofHom ⟨f.hom, fun _ ↦ rfl⟩

/-- A predicate for representations that fix every element. -/
/-
**Rep.IsTrivial** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：IsTrivial (A : Rep k G)
参数：A : Rep k G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate for representations that fix every element.
-/
abbrev IsTrivial (A : Rep k G) := A.ρ.IsTrivial
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : ModuleCat k) : ((trivialFunctor k G).obj X).IsTrivial where
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {V : Type w} [AddCommGroup V] [Module k V] :
    IsTrivial (Rep.trivial k G V) where
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {V : Type w} [AddCommGroup V] [Module k V] (ρ : Representation k G V) [ρ.IsTrivial] :
    IsTrivial (Rep.of ρ) where
  out := Representation.isTrivial_def ρ
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {H : Type u'} {V : Type w} [Group H] [AddCommGroup V] [Module k V]
    (ρ : Representation k H V) (f : G →* H) [Representation.IsTrivial (ρ.comp f)] :
    Representation.IsTrivial ((Rep.of ρ).ρ.comp f) := ‹_›

variable {A B C : Rep.{w} k G}
/-
**Rep.hasForgetToModuleCat** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
形式化陈述：hasForgetToModuleCat : HasForget₂ (Rep.{w} k G) (ModuleCat.{w} k) where fo
rget₂.obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToModuleCat :
    HasForget₂ (Rep.{w} k G) (ModuleCat.{w} k) where
  forget₂.obj A := .of k A
  forget₂.map f := ModuleCat.ofHom f.hom.toLinearMap

/-- A morphism in `Rep k G` has an underlying linear map attached to it hence induce a morphism in
  `ModuleCat k`. -/
/-
**Rep.Hom.toModuleCatHom** 是 Mathlib 中的一个定义，位于命名空间 `Rep.Hom`。
形式化陈述：{k : Type u} →   {G : Type v} →     [inst : Ring k] →       [inst_1 : Mono
id G] → {A B : Rep.{w, u, v} k G} → (A ⟶ B) → (ModuleCat.of k ↑A ⟶ ModuleCat.of 
k ↑B)
参数：A ⟶ B；ModuleCat.of k ↑A ⟶ ModuleCat.of k ↑B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism in `Rep k G` has an underlying linear map attached to it hence induce
 a morphism in
  `ModuleCat k`.
-/
abbrev Hom.toModuleCatHom (f : A ⟶ B) : ModuleCat.of k A.V ⟶ ModuleCat.of k B.V :=
  ModuleCat.ofHom f.hom.toLinearMap
/-
**Rep.forget** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forget₂_moduleCat_obj (A : Rep.{w} k G) :
    (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).obj A = .of k A := rfl
/-
**Rep.forget** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forget₂_moduleCat_map (f : A ⟶ B) :
    (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).map f = ModuleCat.ofHom f.hom.toLinearMap := rfl
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).Faithful := inferInstance

section Action

variable (k G)

set_option backward.isDefEq.respectTransparency.types false in
/-- Every object in `Rep k G` naturally correspond to an object in `Action`. -/
@[simps]
/-
**Rep.RepToAction** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：RepToAction : Rep.{w} k G ⥤ Action (ModuleCat.{w} k) G where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every object in `Rep k G` naturally correspond to an object in `Action`.
-/
def RepToAction : Rep.{w} k G ⥤ Action (ModuleCat.{w} k) G where
  obj X := ⟨.of k X, (ModuleCat.endRingEquiv (.of k X)).symm.toMonoidHom.comp X.ρ⟩
  map f := ⟨f.toModuleCatHom, fun g ↦ ModuleCat.hom_ext <| by
    simp [ModuleCat.endRingEquiv, f.hom.2]⟩
/-
**Rep.RepToAction_obj** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：RepToAction_obj (X : Rep.{w} k G) : (RepToAction k G).obj X = ⟨.of k X, (M
oduleCat.endRingEquiv (.of k X)).symm.toMonoidHom.comp X.ρ⟩
参数：X : Rep.{w} k G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma RepToAction_obj (X : Rep.{w} k G) : (RepToAction k G).obj X =
  ⟨.of k X, (ModuleCat.endRingEquiv (.of k X)).symm.toMonoidHom.comp X.ρ⟩ := rfl

/-- Every object in `ModuleCat k` that `G` acts on is an object in `Rep k G`. -/
@[simps]
/-
**Rep.ActionToRep** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：ActionToRep : Action (ModuleCat.{w} k) G ⥤ Rep.{w} k G where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every object in `ModuleCat k` that `G` acts on is an object in `Rep k G`.
-/
def ActionToRep : Action (ModuleCat.{w} k) G ⥤ Rep.{w} k G where
  obj X := of <| (ModuleCat.endRingEquiv X.V).toMonoidHom.comp X.ρ
  map f := ofHom ⟨f.hom.hom, fun g ↦ by simpa using ModuleCat.hom_ext_iff.1 (f.comm g)⟩

/-- `unitIso` of the equivalence between `Action` and `Rep`. -/
/-
**Rep.RepToAction_ActionToRep** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：RepToAction_ActionToRep (A : Action (ModuleCat.{w} k) G) : (RepToAction k 
G).obj ((ActionToRep k G).obj A) ≅ A where hom
参数：A : Action (ModuleCat.{w} k) G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`unitIso` of the equivalence between `Action` and `Rep`.
-/
def RepToAction_ActionToRep (A : Action (ModuleCat.{w} k) G) :
    (RepToAction k G).obj ((ActionToRep k G).obj A) ≅ A where
  hom := ⟨𝟙 _, fun g ↦ by rfl⟩
  inv := ⟨𝟙 _, fun g ↦ by rfl⟩

/-- `counitIso` of the equivalence between `Action` and `Rep`. -/
/-
**Rep.ActionToRep_RepToAction** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：ActionToRep_RepToAction (X : Rep.{w} k G) : (ActionToRep k G).obj ((RepToA
ction k G).obj X) ≅ X where hom
参数：X : Rep.{w} k G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`counitIso` of the equivalence between `Action` and `Rep`.
-/
def ActionToRep_RepToAction (X : Rep.{w} k G) :
    (ActionToRep k G).obj ((RepToAction k G).obj X) ≅ X where
  hom := ofHom ⟨LinearMap.id, fun g ↦ show LinearMap.id ∘ₗ X.ρ g = X.ρ g ∘ₗ LinearMap.id by simp⟩
  inv := ofHom ⟨LinearMap.id, fun g ↦ show LinearMap.id ∘ₗ X.ρ g = X.ρ g ∘ₗ LinearMap.id by simp⟩

/-- The category equivalence between `Rep` and `Action`. -/
/-
**Rep.repIsoAction** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：repIsoAction : Rep.{w} k G ≌ Action (ModuleCat.{w} k) G where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category equivalence between `Rep` and `Action`.
-/
def repIsoAction : Rep.{w} k G ≌ Action (ModuleCat.{w} k) G where
  functor := RepToAction k G
  inverse := ActionToRep k G
  unitIso := NatIso.ofComponents (ActionToRep_RepToAction k G)
  counitIso := NatIso.ofComponents (RepToAction_ActionToRep k G)
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (RepToAction k G).IsEquivalence :=
  repIsoAction k G |>.isEquivalence_functor
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (ActionToRep k G).IsEquivalence :=
  repIsoAction k G |>.isEquivalence_inverse
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).Additive where
  map_add {X Y} f g := by ext1; simp [add_hom]

/-- Forgetting `Rep` to `ModuleCat` is the same as first map to `Action`
  then forget to `ModuleCat`. -/
/-
**Rep.forgetNatIsoActionForget** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：forgetNatIsoActionForget : forget₂ (Rep.{w} k G) (ModuleCat k) ≅ (RepToAct
ion k G) ⋙ Action.forget (ModuleCat k) G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Forgetting `Rep` to `ModuleCat` is the same as first map to `Action`
  then forget to `ModuleCat`.
-/
abbrev forgetNatIsoActionForget : forget₂ (Rep.{w} k G) (ModuleCat k) ≅ (RepToAction k G) ⋙
    Action.forget (ModuleCat k) G := .refl _
/-
**Rep.preservesLimits_forget** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
形式化陈述：preservesLimits_forget : Limits.PreservesLimitsOfSize.{w, w} (forget₂ (Rep
.{w} k G) (ModuleCat k))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimits_of_natIso`：preservesLimits_of_natI
so {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfSize.{w, w'} F] : PreservesLimits
OfSize.{w, w'} G where preservesLimit…
· 使用定理 `CategoryTheory.Limits.comp_preservesLimits`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {E : Type u₃} [ℰ :…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`：∀ {C :
 Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `Rep.instIsEquivalenceActionModuleCatRepToAction`：∀ (k : Type u) (G : Typ
e v) [inst : Ring k] [inst_1 : Monoid G], (Rep.RepToAction k G).IsEquivalence
· 使用定理 `ModuleCat.instHasLimitsOfSize`：∀ {R : Type u} [inst : Ring R],   Categor
yTheory.Limits.HasLimitsOfSize.{v, v, max v w, max (max (v + 1) (w + 1)) u} (Mod
uleCat R)
-/
instance preservesLimits_forget :
    Limits.PreservesLimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (ModuleCat k)) :=
  Limits.preservesLimits_of_natIso (forgetNatIsoActionForget k G).symm
/-
**Rep.preservesColimits_forget** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
形式化陈述：preservesColimits_forget : Limits.PreservesColimitsOfSize.{w, w} (forget₂ 
(Rep.{w} k G) (ModuleCat k))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimits_of_natIso`：preservesColimits_of_
natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfSize.{w, w'} F] : Preserves
ColimitsOfSize.{w, w'} G where preserve…
· 使用定理 `CategoryTheory.Limits.comp_preservesColimits`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {E : Type u₃} [ℰ :…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint`：∀ {C 
: Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst
_1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `Rep.instIsEquivalenceActionModuleCatRepToAction`：∀ (k : Type u) (G : Typ
e v) [inst : Ring k] [inst_1 : Monoid G], (Rep.RepToAction k G).IsEquivalence
· 使用定理 `ModuleCat.hasColimitsOfSize`：∀ (R : Type w) [inst : Ring R] [CategoryThe
ory.Limits.HasColimitsOfSize.{v, u, w', w' + 1} AddCommGrpCat],   CategoryTheory
.Limits.HasColimi…
· 使用定理 `AddCommGrpCat.hasColimitsOfSize`：∀ [UnivLE.{u, w}], CategoryTheory.Limit
s.HasColimitsOfSize.{v, u, w, w + 1} AddCommGrpCat
-/
instance preservesColimits_forget :
    Limits.PreservesColimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (ModuleCat k)) :=
  Limits.preservesColimits_of_natIso (forgetNatIsoActionForget k G).symm
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Limits.HasBinaryBiproducts (Rep.{w} k G) where
  has_binary_biproduct A B := Limits.hasBinaryBiproduct_of_total
    ⟨Rep.of (X := A.V × B.V) (A.ρ.prod B.ρ), Rep.ofHom (.fst k A.ρ B.ρ), Rep.ofHom (.snd k A.ρ B.ρ),
      Rep.ofHom (.inl k A.ρ B.ρ), Rep.ofHom (.inr k A.ρ B.ρ), by ext1; simp,
      by ext1; simp [zero_hom], by ext1; simp [zero_hom], by ext1; simp⟩ <| by
    ext1; simp [Rep.add_hom]
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Limits.HasZeroObject (Rep.{w} k G) where
  zero := ⟨Rep.trivial k G PUnit, {
    unique_to X := Nonempty.intro ⟨⟨0⟩, fun f ↦ by
      ext x; have : x = 0 := Subsingleton.elim _ _; subst this; simp⟩
    unique_from X := Nonempty.intro ⟨⟨0⟩, fun f ↦ by ext⟩
  }⟩

/-- An object of `Rep k G` is zero iff the underlying `k`-module is zero. -/
/-
**Rep.isZero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：isZero_iff (M : Rep k G) : Limits.IsZero M ↔ Subsingleton M.V
参数：M : Rep k G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ModuleCat.isZero_of_iff_subsingleton`：isZero_of_iff_subsingleton {M : Ty
pe*} [AddCommGroup M] [Module R M] : IsZero (of R M) ↔ Subsingleton M
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An object of `Rep k G` is zero iff the underlying `k`-module is zero.
-/
lemma isZero_iff (M : Rep k G) : Limits.IsZero M ↔ Subsingleton M.V := by
  simp [Limits.IsZero.iff_id_eq_zero, Rep.hom_ext_iff, Representation.IntertwiningMap.ext_iff,
    ← ModuleCat.isZero_of_iff_subsingleton (R := k), ModuleCat.hom_ext_iff]
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Limits.HasLimits (Rep.{w} k G) :=
  Adjunction.has_limits_of_equivalence (repIsoAction k G).functor
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Limits.HasColimits (Rep.{w} k G) :=
  Adjunction.has_colimits_of_equivalence (repIsoAction k G).functor
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Limits.ReflectsLimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (ModuleCat k)) :=
  Limits.reflectsLimits_of_reflectsIsomorphisms
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Limits.ReflectsColimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (ModuleCat k)) :=
  Limits.reflectsColimits_of_reflectsIsomorphisms
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Abelian (Rep.{w} k G) := abelianOfEquivalence (RepToAction k G)

variable {k G} in
/-
**Rep.epi_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Rep`。
形式化陈述：epi_iff_surjective (f : A ⟶ B) : Epi f ↔ Function.Surjective f.hom
参数：f : A ⟶ B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ModuleCat.epi_iff_surjective`：epi_iff_surjective : Epi f ↔ Function.Surj
ective f
· 使用定理 `CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape`：∀ {C :
 Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.epi_of_epi_map`：epi_of_epi_map (F : C ⥤ D) [Refle
ctsEpimorphisms F] {X Y : C} {f : X ⟶ Y} (h : Epi (F.map f)) : Epi f
· 使用定理 `CategoryTheory.reflectsEpimorphisms_of_reflectsColimitsOfShape`：∀ {C : T
ype u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteColimits.reflects`：∀ {C : Type u₁} {
inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheor
y.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Abelian.hasFiniteColimits`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.H
asFiniteColimits C
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem epi_iff_surjective (f : A ⟶ B) : Epi f ↔ Function.Surjective f.hom :=
  ⟨fun _ => (ModuleCat.epi_iff_surjective ((forget₂ _ _).map f)).1 inferInstance,
  fun h => (forget₂ _ _).epi_of_epi_map ((ModuleCat.epi_iff_surjective <|
    (forget₂ _ _).map f).2 h)⟩

variable {k G} in
/-
**Rep.mono_iff_injective** 是 Mathlib 中的一个定理，位于命名空间 `Rep`。
形式化陈述：mono_iff_injective (f : A ⟶ B) : Mono f ↔ Function.Injective f.hom
参数：f : A ⟶ B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ModuleCat.mono_iff_injective`：mono_iff_injective : Mono f ↔ Function.Inj
ective f
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape`：∀ {C : 
Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.mono_of_mono_map`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.reflectsMonomorphisms_of_reflectsLimitsOfShape`：∀ {C : Ty
pe u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteLimits.reflects`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.
Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem mono_iff_injective (f : A ⟶ B) : Mono f ↔ Function.Injective f.hom :=
  ⟨fun _ => (ModuleCat.mono_iff_injective ((forget₂ _ _).map f)).1 inferInstance,
  fun h => (forget₂ _ _).mono_of_mono_map ((ModuleCat.mono_iff_injective <|
    (forget₂ _ _).map f).2 h)⟩
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : A ⟶ B) [Mono f] : Mono f.toModuleCatHom :=
  inferInstanceAs <| Mono ((forget₂ _ _).map f)
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : A ⟶ B) [Epi f] : Epi f.toModuleCatHom :=
  inferInstanceAs <| Epi ((forget₂ _ _).map f)

end Action

end ring

section CommSemiring

variable {k : Type u} {G : Type v} [CommSemiring k] [Monoid G]

/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N : Rep k G} : SMul k (M ⟶ N) where
  smul r f := ofHom (r • f.hom)
/-
**Rep.ofHom_smul** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：ofHom_smul {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module k M] [
Module k N] {σ : Representation k G M} {ρ : Representation k G N} (f : σ.Intertw
iningMap ρ) (r : k) : ofHom (r • f) = r • ofHom f
参数：f : σ.IntertwiningMap ρ；r : k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_smul {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
    {σ : Representation k G M} {ρ : Representation k G N} (f : σ.IntertwiningMap ρ) (r : k) :
    ofHom (r • f) = r • ofHom f := rfl
/-
**Rep.smul_hom** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：smul_hom {M N : Rep k G} (f : M ⟶ N) (r : k) : (r • f).hom = r • f.hom
参数：f : M ⟶ N；r : k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_hom {M N : Rep k G} (f : M ⟶ N) (r : k) : (r • f).hom = r • f.hom := rfl
/-
**Rep.smul_comp** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：smul_comp {M N O : Rep k G} (r : k) (f : M ⟶ N) (g : N ⟶ O) : (r • f) ≫ g 
= r • (f ≫ g)
参数：r : k；f : M ⟶ N；g : N ⟶ O。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rep.hom_ext`：∀ {k : Type u} {G : Type v} [inst : Semiring k] [inst_1 : M
onoid G] {A B : Rep.{w, u, v} k G} {f g : A ⟶ B},   Rep.Hom.hom f = Rep.Hom.hom 
g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Representation.IntertwiningMap.comp_smul`：comp_smul (a : A) (f : Intertw
iningMap σ τ) (g : IntertwiningMap ρ σ) : comp f (a • g) = a • comp f g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smul_comp {M N O : Rep k G} (r : k) (f : M ⟶ N) (g : N ⟶ O) :
    (r • f) ≫ g = r • (f ≫ g) := by
  ext1
  simp [smul_hom, Representation.IntertwiningMap.comp_smul]
/-
**Rep.comp_smul** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：comp_smul {M N O : Rep k G} (f : M ⟶ N) (r : k) (g : N ⟶ O) : f ≫ (r • g) 
= r • (f ≫ g)
参数：f : M ⟶ N；r : k；g : N ⟶ O。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rep.hom_ext`：∀ {k : Type u} {G : Type v} [inst : Semiring k] [inst_1 : M
onoid G] {A B : Rep.{w, u, v} k G} {f g : A ⟶ B},   Rep.Hom.hom f = Rep.Hom.hom 
g…
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Representation.IntertwiningMap.smul_comp`：smul_comp (a : A) (f : Intertw
iningMap σ τ) (g : IntertwiningMap ρ σ) : (a • f).comp g = a • comp f g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_smul {M N O : Rep k G} (f : M ⟶ N) (r : k) (g : N ⟶ O) :
    f ≫ (r • g) = r • (f ≫ g) := by
  ext
  simp [smul_hom, Representation.IntertwiningMap.smul_comp]
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N : Rep k G} : Module k (M ⟶ N) := fast_instance% hom_injective.module
  _ ⟨⟨_, zero_hom⟩, add_hom⟩ <| by simp [smul_hom]
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Linear k (Rep k G) where
  smul_comp _ _ _ := smul_comp
  comp_smul _ _ _ := comp_smul

end CommSemiring

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Functor.Linear k (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)) where
  map_smul {X Y} f r := by
    ext
    simp [smul_hom]

/-- The equivalence between `IntertwiningMap`s and morphism between `X Y : Rep k G` is linear. -/
/-
**Rep.homLinearEquiv** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：homLinearEquiv (X Y : Rep k G) : (X ⟶ Y) ≃ₗ[k] (X.ρ.IntertwiningMap Y.ρ) w
here __
参数：X Y : Rep k G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `IntertwiningMap`s and morphism between `X Y : Rep k G` 
is linear.
-/
abbrev homLinearEquiv (X Y : Rep k G) : (X ⟶ Y) ≃ₗ[k] (X.ρ.IntertwiningMap Y.ρ) where
  __ := homEquiv
  map_add' := add_hom
  map_smul' _ _ := smul_hom _ _

section monoidal

open MonoidalCategory CategoryTheory Representation.IntertwiningMap
  Representation.TensorProduct

/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidalCategory (Rep.{u} k G) where
  tensorObj X Y := of (X.ρ.tprod Y.ρ)
  whiskerLeft X _ _ f := ofHom (lTensor X.ρ f.hom)
  whiskerRight f Z := ofHom (rTensor Z.ρ f.hom)
  tensorUnit := Rep.trivial k G k
  tensorHom f g := ofHom (f.hom.tensor g.hom)
  associator X Y Z := Rep.mkIso (assoc X.ρ Y.ρ Z.ρ)
  leftUnitor X := Rep.mkIso (lid k X.ρ)
  rightUnitor X := Rep.mkIso (rid k X.ρ)
  associator_naturality _ _ _ := by ext; simp
  leftUnitor_naturality _ := by ext; simp [trivial_V]
  rightUnitor_naturality _ := by ext; simp [trivial_V]
  pentagon _ _ _ _ := by ext; simp
  triangle X Y := by ext; simp

@[simp]
/-
**Rep.tensorUnit_V** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：tensorUnit_V : (𝟙_ (Rep.{u} k G)).V = k
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorUnit_V : (𝟙_ (Rep.{u} k G)).V = k := rfl

@[simp]
/-
**Rep.tensorUnit_** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorUnit_ρ : (𝟙_ (Rep.{u} k G)).ρ = Representation.trivial k G k := rfl

@[simp]
/-
**Rep.tensor_V** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：tensor_V {X Y : Rep k G} : (X otimes Y).V = TensorProduct k X.V Y.V
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensor_V {X Y : Rep k G} : (X ⊗ Y).V = TensorProduct k X.V Y.V := rfl

@[simp]
/-
**Rep.tensor_** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensor_ρ {X Y : Rep k G} : (X ⊗ Y).ρ = X.ρ.tprod Y.ρ := rfl

@[simp]
/-
**Rep.hom_whiskerRight** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：hom_whiskerRight {X₁ X₂ Y : Rep k G} (f : X₁ ⟶ X₂) : (f ▷ Y).hom = .rTenso
r _ f.hom
参数：f : X₁ ⟶ X₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_whiskerRight {X₁ X₂ Y : Rep k G} (f : X₁ ⟶ X₂) :
    (f ▷ Y).hom = .rTensor _ f.hom := rfl

@[simp]
/-
**Rep.hom_whiskerLeft** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：hom_whiskerLeft {X Y₁ Y₂ : Rep k G} (f : Y₁ ⟶ Y₂) : (X ◁ f).hom = .lTensor
 _ f.hom
参数：f : Y₁ ⟶ Y₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_whiskerLeft {X Y₁ Y₂ : Rep k G} (f : Y₁ ⟶ Y₂) :
    (X ◁ f).hom = .lTensor _ f.hom := rfl

@[simp]
/-
**Rep.hom_tensorHom** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：hom_tensorHom {X₁ X₂ Y₁ Y₂ : Rep k G} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : (f oti
mesₘ g).hom = f.hom.tensor g.hom
参数：f : X₁ ⟶ Y₁；g : X₂ ⟶ Y₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_tensorHom {X₁ X₂ Y₁ Y₂ : Rep k G} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g).hom = f.hom.tensor g.hom := rfl

@[simp]
/-
**Rep.of_tensor** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：of_tensor {X Y : Type u} [AddCommGroup X] [AddCommGroup Y] [Module k X] [M
odule k Y] (σ : Representation k G X) (ρ : Representation k G Y) : of (σ.tprod ρ
) = of σ otimes of ρ
参数：σ : Representation k G X；ρ : Representation k G Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_tensor {X Y : Type u} [AddCommGroup X] [AddCommGroup Y] [Module k X] [Module k Y]
    (σ : Representation k G X) (ρ : Representation k G Y) :
    of (σ.tprod ρ) = of σ ⊗ of ρ := rfl

@[simp]
/-
**Rep.hom_hom_associator** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：hom_hom_associator {X Y Z : Rep k G} : (α_ X Y Z).hom.hom = (Representatio
n.TensorProduct.assoc X.ρ Y.ρ Z.ρ).toIntertwiningMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
· 使用定理 `TensorProduct.ext_threefold`：ext_threefold {g h : M otimes[R] N otimes[R
] P ->ₛₗ[σ₁₂] P₂} (H : forall x y z, g (x otimesₜ y otimesₜ z) = h (x otimesₜ y 
otimesₜ z)) : g =…
-/
lemma hom_hom_associator {X Y Z : Rep k G} : (α_ X Y Z).hom.hom =
    (Representation.TensorProduct.assoc X.ρ Y.ρ Z.ρ).toIntertwiningMap := by
  ext1
  refine TensorProduct.ext_threefold fun x y z ↦ by rfl

@[simp]
/-
**Rep.hom_inv_associator** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：hom_inv_associator {X Y Z : Rep k G} : (α_ X Y Z).inv.hom = (Representatio
n.TensorProduct.assoc X.ρ Y.ρ Z.ρ).symm.toIntertwiningMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_inv_associator {X Y Z : Rep k G} : (α_ X Y Z).inv.hom =
    (Representation.TensorProduct.assoc X.ρ Y.ρ Z.ρ).symm.toIntertwiningMap := rfl

@[simp]
/-
**Rep.hom_hom_leftUnitor** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：hom_hom_leftUnitor {X : Rep k G} : (fun_ X).hom.hom = (Representation.Tens
orProduct.lid k X.ρ).toIntertwiningMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_hom_leftUnitor {X : Rep k G} : (λ_ X).hom.hom =
    (Representation.TensorProduct.lid k X.ρ).toIntertwiningMap :=
  rfl

@[simp]
/-
**Rep.hom_inv_leftUnitor** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：hom_inv_leftUnitor {X : Rep k G} : (fun_ X).inv.hom = (Representation.Tens
orProduct.lid k X.ρ).symm.toIntertwiningMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_inv_leftUnitor {X : Rep k G} : (λ_ X).inv.hom =
    (Representation.TensorProduct.lid k X.ρ).symm.toIntertwiningMap := rfl

@[simp]
/-
**Rep.hom_hom_rightUnitor** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：hom_hom_rightUnitor {X : Rep k G} : (ρ_ X).hom.hom = (Representation.Tenso
rProduct.rid k X.ρ).toIntertwiningMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_hom_rightUnitor {X : Rep k G} : (ρ_ X).hom.hom =
    (Representation.TensorProduct.rid k X.ρ).toIntertwiningMap :=
  rfl

@[simp]
/-
**Rep.hom_inv_rightUnitor** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：hom_inv_rightUnitor {X : Rep k G} : (ρ_ X).inv.hom = (Representation.Tenso
rProduct.rid k X.ρ).symm.toIntertwiningMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_inv_rightUnitor {X : Rep k G} : (ρ_ X).inv.hom =
    (Representation.TensorProduct.rid k X.ρ).symm.toIntertwiningMap := rfl
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidalPreadditive (Rep.{u} k G) where
  whiskerLeft_zero {_ _ _} := by ext1; simp
  zero_whiskerRight {_ _ _} := by ext1; simp
  whiskerLeft_add _ _ := by ext1; simp [add_hom]
  add_whiskerRight _ _ := by ext1; simp [add_hom]
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidalLinear k (Rep.{u} k G) where
  whiskerLeft_smul _ _ _ _ _ := by ext1; simp [smul_hom]
  smul_whiskerRight _ _ _ _ _ := by ext1; simp [smul_hom]
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BraidedCategory (Rep.{u} k G) where
  braiding X Y := Rep.mkIso (Representation.TensorProduct.comm X.ρ Y.ρ)
  braiding_naturality_right _ _ _ _ := by ext1; simp [comm_comp_lTensor]
  braiding_naturality_left _ _ := by ext1; simp [comm_comp_rTensor]
  hexagon_forward _ _ _ := by
    ext : 2
    exact TensorProduct.ext_threefold <| fun _ _ _ ↦ by simp
  hexagon_reverse X Y Z := by
    ext : 2
    simp only [tensor_V, tensor_ρ, hom_comp, hom_inv_associator, mkIso_hom_hom, comp_toLinearMap,
      assoc_symm_toLinearMap, toLinearMap_comm, LinearEquiv.comp_coe, hom_whiskerRight,
      hom_whiskerLeft, toLinearMap_rTensor, toLinearMap_lTensor]
    ext; simp

@[simp]
/-
**Rep.hom_braiding** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：hom_braiding {X Y : Rep k G} : (β_ X Y).hom.hom = (Representation.TensorPr
oduct.comm X.ρ Y.ρ).toIntertwiningMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_braiding {X Y : Rep k G} : (β_ X Y).hom.hom =
    (Representation.TensorProduct.comm X.ρ Y.ρ).toIntertwiningMap := rfl

open Representation.Equiv in
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SymmetricCategory (Rep.{u} k G) where
  symmetry X Y := by ext1; simp [← comm_symm Y.ρ X.ρ, ← toIntertwiningMap_trans,
    trans_symm, toIntertwiningMap_refl]

end monoidal

section MonoidalClosed
open MonoidalCategory Action

variable {G : Type v} [Group G] (A B C : Rep.{w} k G)

/-- Given a `k`-linear `G`-representation `(A, ρ₁)`, this is the 'internal Hom' functor sending
`(B, ρ₂)` to the representation `Homₖ(A, B)` that maps `g : G` and `f : A →ₗ[k] B` to
`(ρ₂ g) ∘ₗ f ∘ₗ (ρ₁ g⁻¹)`. -/
@[simps]
/-
**Rep.ihom** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：{k : Type u} →   [inst : CommRing k] →     {G : Type v} →       [inst_1 : 
Group G] → Rep.{w, u, v} k G → CategoryTheory.Functor (Rep.{u_1, u, v} k G) (Rep
.{max w u_1, u, v} k G)
参数：Rep.{u_1, u, v} k G；Rep.{max w u_1, u, v} k G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `k`-linear `G`-representation `(A, ρ₁)`, this is the 'internal Hom' func
tor sending
`(B, ρ₂)` to the representation `Homₖ(A, B)` that maps `g : G` and `f : A →ₗ[k] 
B` to
`(ρ₂ g) ∘ₗ f ∘ₗ (ρ₁ g⁻¹)`.
-/
protected noncomputable def ihom : Rep k G ⥤ Rep k G where
  obj B := Rep.of (Representation.linHom A.ρ B.ρ)
  map {X} {Y} f := Rep.ofHom ⟨LinearMap.llcomp k _ _ _ f.hom.toLinearMap, fun g ↦ by
    ext; simp [Representation.IntertwiningMap.toLinearMap_apply, ← hom_comm_apply]⟩
  map_id := fun _ => by ext; rfl
  map_comp := fun _ _ => by ext; rfl
/-
**Rep.ihom_obj_** 是 Mathlib 中的一个定理，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ihom_obj_ρ_apply {A B : Rep k G} (g : G) (x : A →ₗ[k] B) :
    -- Hint to put this lemma into `simp`-normal form.
    DFunLike.coe (F := (Representation k G (↑A.V →ₗ[k] ↑B.V)))
    ((Rep.ihom A).obj B).ρ g x = B.ρ g ∘ₗ x ∘ₗ A.ρ g⁻¹ :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a `k`-linear `G`-representation `A`, this is the Hom-set bijection in the adjunction
`A ⊗ - ⊣ ihom(A, -)`. It sends `f : A ⊗ B ⟶ C` to a `Rep k G` morphism defined by currying the
`k`-linear map underlying `f`, giving a map `A →ₗ[k] B →ₗ[k] C`, then flipping the arguments. -/
@[simps]
/-
**Rep.tensorHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：tensorHomEquiv (A B C : Rep.{u} k G) : (A otimes B ⟶ C) ≃ (B ⟶ (Rep.ihom A
).obj C) where toFun f
参数：A B C : Rep.{u} k G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `k`-linear `G`-representation `A`, this is the Hom-set bijection in the 
adjunction
`A ⊗ - ⊣ ihom(A, -)`. It sends `f : A ⊗ B ⟶ C` to a `Rep k G` morphism defined b
y currying the
`k`-linear map underlying `f`, giving a map `A →ₗ[k] B →ₗ[k] C`, then flipping t
he arguments.
-/
def tensorHomEquiv (A B C : Rep.{u} k G) : (A ⊗ B ⟶ C) ≃ (B ⟶ (Rep.ihom A).obj C) where
  toFun f := Rep.ofHom ⟨(TensorProduct.curry f.hom.toLinearMap).flip, fun g ↦ by
    ext x y
    simp only [tensor_V, tensor_ρ, LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
      TensorProduct.curry_apply, Representation.IntertwiningMap.toLinearMap_apply,
      Representation.linHom_apply]
    have := by simpa using (hom_comm_apply f g (A.ρ g⁻¹ y ⊗ₜ[k] x)).symm
    simp [this]⟩
  invFun f := Rep.ofHom ⟨TensorProduct.uncurry (.id k) _ _ _
    f.hom.toLinearMap.flip, fun g ↦ TensorProduct.ext' fun x y => by
    simpa using LinearMap.ext_iff.1 (hom_comm_apply f g y) (A.ρ g x)⟩
  left_inv _ := Rep.Hom.ext <| Representation.IntertwiningMap.ext <|
    TensorProduct.ext' fun _ _ => rfl

variable {A B C}
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : MonoidalClosed (Rep k G) where
  closed A :=
    { rightAdj := Rep.ihom A
      adj := Adjunction.mkOfHomEquiv ({
        homEquiv := Rep.tensorHomEquiv A
        homEquiv_naturality_left_symm := fun _ _ => Rep.hom_ext <|
          Representation.IntertwiningMap.ext <| TensorProduct.ext' fun _ _ => rfl
        homEquiv_naturality_right _ _ := Rep.hom_ext <|
          Representation.IntertwiningMap.ext <|
            LinearMap.ext fun _ ↦ LinearMap.ext fun _ => rfl }) }

@[simp]
/-
**Rep.ihom_obj_** 是 Mathlib 中的一个定理，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ihom_obj_ρ_def (A B : Rep k G) : ((ihom A).obj B).ρ = ((Rep.ihom A).obj B).ρ :=
  rfl

@[simp]
/-
**Rep.homEquiv_def** 是 Mathlib 中的一个定理，位于命名空间 `Rep`。
形式化陈述：homEquiv_def (A B C : Rep k G) : (ihom.adjunction A).homEquiv B C = Rep.te
nsorHomEquiv A B C
参数：A B C : Rep k G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Adjunction.mkOfHomEquiv_homEquiv`：mkOfHomEquiv_homEquiv (
adj : CoreHomEquiv F G) : (mkOfHomEquiv adj).homEquiv = adj.homEquiv
-/
theorem homEquiv_def (A B C : Rep k G) : (ihom.adjunction A).homEquiv B C =
    Rep.tensorHomEquiv A B C :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) _) _

@[simp]
/-
**Rep.ihom_ev_app_hom** 是 Mathlib 中的一个定理，位于命名空间 `Rep`。
形式化陈述：ihom_ev_app_hom (A B : Rep k G) : ((ihom.ev A).app B).hom.toLinearMap = (T
ensorProduct.uncurry (.id k) A (A ->ₗ[k] B) B LinearMap.id.flip)
参数：A B : Rep k G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem ihom_ev_app_hom (A B : Rep k G) :
    ((ihom.ev A).app B).hom.toLinearMap = (TensorProduct.uncurry (.id k) A (A →ₗ[k] B) B
      LinearMap.id.flip) := by
  ext; rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Rep.ihom_coev_app_hom** 是 Mathlib 中的一个定理，位于命名空间 `Rep`。
形式化陈述：∀ {k : Type u} [inst : CommRing k] {G : Type v} [inst_1 : Group G] (A B : 
Rep.{u, u, v} k G),   (Rep.Hom.hom ((CategoryTheory.ihom.coev A).app B)).toLinea
rMap =     (TensorProduct.mk k ↑A ↑((CategoryTheory.Functor.id (Rep.{u, u, v} k 
G)).obj B)).flip
参数：A B : Rep.{u, u, v} k G；Rep.Hom.hom ((CategoryTheory.ihom.coev A).app B)；Tens
orProduct.mk k ↑A ↑((CategoryTheory.Functor.id (Rep.{u, u, v} k G)).obj B)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
@[simp] theorem ihom_coev_app_hom (A B : Rep k G) :
    ((ihom.coev A).app B).hom.toLinearMap = (TensorProduct.mk k _ _).flip :=
  LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

/-- There is a `k`-linear isomorphism between the sets of representation morphisms `Hom(A ⊗ B, C)`
and `Hom(B, Homₖ(A, C))`. -/
/-
**Rep.MonoidalClosed.linearHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Rep.MonoidalClose
d`。
形式化陈述：{k : Type u} →   [inst : CommRing k] →     {G : Type v} →       [inst_1 : 
Group G] →         (A B C : Rep.{u, u, v} k G) → (CategoryTheory.MonoidalCategor
yStruct.tensorObj A B ⟶ C) ≃ₗ[k] B ⟶ A ⟹ C
参数：A B C : Rep.{u, u, v} k G；CategoryTheory.MonoidalCategoryStruct.tensorObj A B
 ⟶ C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a `k`-linear isomorphism between the sets of representation morphisms `
Hom(A ⊗ B, C)`
and `Hom(B, Homₖ(A, C))`.
-/
def MonoidalClosed.linearHomEquiv (A B C : Rep.{u} k G) : (A ⊗ B ⟶ C) ≃ₗ[k] B ⟶ A ⟶[Rep k G] C :=
  { (ihom.adjunction A).homEquiv _ _ with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- There is a `k`-linear isomorphism between the sets of representation morphisms `Hom(A ⊗ B, C)`
and `Hom(A, Homₖ(B, C))`. -/
/-
**Rep.MonoidalClosed.linearHomEquivComm** 是 Mathlib 中的一个定义，位于命名空间 `Rep.MonoidalC
losed`。
形式化陈述：{k : Type u} →   [inst : CommRing k] →     {G : Type v} →       [inst_1 : 
Group G] →         (A B C : Rep.{u, u, v} k G) → (CategoryTheory.MonoidalCategor
yStruct.tensorObj A B ⟶ C) ≃ₗ[k] A ⟶ B ⟹ C
参数：A B C : Rep.{u, u, v} k G；CategoryTheory.MonoidalCategoryStruct.tensorObj A B
 ⟶ C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a `k`-linear isomorphism between the sets of representation morphisms `
Hom(A ⊗ B, C)`
and `Hom(A, Homₖ(B, C))`.
-/
def MonoidalClosed.linearHomEquivComm (A B C : Rep.{u} k G) : (A ⊗ B ⟶ C) ≃ₗ[k] A ⟶ B
    ⟶[Rep k G] C :=
  Linear.homCongr k (β_ A B) (Iso.refl _) ≪≫ₗ MonoidalClosed.linearHomEquiv _ _ _

@[simp]
/-
**Rep.MonoidalClosed.linearHomEquiv_hom** 是 Mathlib 中的一个定理，位于命名空间 `Rep.MonoidalC
losed`。
形式化陈述：∀ {k : Type u} [inst : CommRing k] {G : Type v} [inst_1 : Group G] (A B C 
: Rep.{u, u, v} k G)   (f : CategoryTheory.MonoidalCategoryStruct.tensorObj A B 
⟶ C),   (Rep.Hom.hom ((Rep.MonoidalClosed.linearHomEquiv A B C) f)).toLinearMap 
=     (TensorProduct.curry (Rep.Hom.hom f).toLinearMap).flip
参数：A B C : Rep.{u, u, v} k G；f : CategoryTheory.MonoidalCategoryStruct.tensorObj
 A B ⟶ C；Rep.Hom.hom ((Rep.MonoidalClosed.linearHomEquiv A B C) f)；TensorProduct
.curry (Rep.Hom.hom f).toLinearMap。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonoidalClosed.linearHomEquiv_hom (A B C : Rep.{u} k G) (f : A ⊗ B ⟶ C) :
    (MonoidalClosed.linearHomEquiv A B C f).hom.toLinearMap =
    (TensorProduct.curry f.hom.toLinearMap).flip :=
  rfl

@[simp]
/-
**Rep.MonoidalClosed.linearHomEquivComm_hom** 是 Mathlib 中的一个定理，位于命名空间 `Rep.Monoi
dalClosed`。
形式化陈述：∀ {k : Type u} [inst : CommRing k] {G : Type v} [inst_1 : Group G] (A B C 
: Rep.{u, u, v} k G)   (f : CategoryTheory.MonoidalCategoryStruct.tensorObj A B 
⟶ C),   (Rep.Hom.hom ((Rep.MonoidalClosed.linearHomEquivComm A B C) f)).toLinear
Map =     TensorProduct.curry (Rep.Hom.hom f).toLinearMap
参数：A B C : Rep.{u, u, v} k G；f : CategoryTheory.MonoidalCategoryStruct.tensorObj
 A B ⟶ C；Rep.Hom.hom ((Rep.MonoidalClosed.linearHomEquivComm A B C) f)；Rep.Hom.h
om f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonoidalClosed.linearHomEquivComm_hom (A B C : Rep.{u} k G) (f : A ⊗ B ⟶ C) :
    (MonoidalClosed.linearHomEquivComm A B C f).hom.toLinearMap =
    TensorProduct.curry f.hom.toLinearMap :=
  rfl
/-
**Rep.MonoidalClosed.linearHomEquiv_symm_hom** 是 Mathlib 中的一个定理，位于命名空间 `Rep.Mono
idalClosed`。
形式化陈述：∀ {k : Type u} [inst : CommRing k] {G : Type v} [inst_1 : Group G] (A B C 
: Rep.{u, u, v} k G) (f : B ⟶ A ⟹ C),   (Rep.Hom.hom ((Rep.MonoidalClosed.linear
HomEquiv A B C).symm f)).toLinearMap =     (TensorProduct.uncurry (RingHom.id k)
 ↑A ↑B ↑C) (Rep.Hom.hom f).flip
参数：A B C : Rep.{u, u, v} k G；f : B ⟶ A ⟹ C；Rep.Hom.hom ((Rep.MonoidalClosed.line
arHomEquiv A B C).symm f)；TensorProduct.uncurry (RingHom.id k) ↑A ↑B ↑C；Rep.Hom.
hom f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rep.homEquiv_def`：homEquiv_def (A B C : Rep k G) : (ihom.adjunction A).h
omEquiv B C = Rep.tensorHomEquiv A B C
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearEquiv.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Sem
iring R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomI
nvPair σ σ'] [i…
-/
theorem MonoidalClosed.linearHomEquiv_symm_hom (A B C : Rep.{u} k G) (f : B ⟶ A ⟶[Rep k G] C) :
    ((MonoidalClosed.linearHomEquiv A B C).symm f).hom.toLinearMap =
      TensorProduct.uncurry (.id k) A B C f.hom.toLinearMap.flip := by
  simp [linearHomEquiv]
  rfl
/-
**Rep.MonoidalClosed.linearHomEquivComm_symm_hom** 是 Mathlib 中的一个定理，位于命名空间 `Rep.
MonoidalClosed`。
形式化陈述：∀ {k : Type u} [inst : CommRing k] {G : Type v} [inst_1 : Group G] (A B C 
: Rep.{u, u, v} k G) (f : A ⟶ B ⟹ C),   (Rep.Hom.hom ((Rep.MonoidalClosed.linear
HomEquivComm A B C).symm f)).toLinearMap =     (TensorProduct.uncurry (RingHom.i
d k) ↑A ↑B ↑C) (Rep.Hom.hom f).toLinearMap
参数：A B C : Rep.{u, u, v} k G；f : A ⟶ B ⟹ C；Rep.Hom.hom ((Rep.MonoidalClosed.line
arHomEquivComm A B C).symm f)；TensorProduct.uncurry (RingHom.id k) ↑A ↑B ↑C；Rep.
Hom.hom f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem MonoidalClosed.linearHomEquivComm_symm_hom (A B C : Rep.{u} k G) (f : A ⟶ B ⟶[Rep k G] C) :
    ((MonoidalClosed.linearHomEquivComm A B C).symm f).hom.toLinearMap =
      TensorProduct.uncurry (.id k) A B C f.hom.toLinearMap :=
  TensorProduct.ext' fun _ _ => rfl

end MonoidalClosed

section

variable {k : Type u} [Semiring k] {G : Type v} [Group G] [Fintype G] (A : Rep.{w} k G)

/-- Given a representation `A` of a finite group `G`, `norm A` is the representation morphism
`A ⟶ A` defined by `x ↦ ∑ A.ρ g x` for `g` in `G`. -/
/-
**Rep.norm** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：norm : End A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a representation `A` of a finite group `G`, `norm A` is the representation
 morphism
`A ⟶ A` defined by `x ↦ ∑ A.ρ g x` for `g` in `G`.
-/
def norm : End A := Rep.ofHom (σ := A.ρ) (ρ := A.ρ) ⟨Representation.norm A.ρ,
    fun g ↦ by ext; simp⟩

@[simp]
/-
**Rep.norm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：norm_apply {x : A} : (norm A).hom x = A.ρ.norm x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma norm_apply {x : A} : (norm A).hom x = A.ρ.norm x := rfl

@[reassoc, elementwise]
/-
**Rep.norm_comm** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：norm_comm {A B : Rep k G} (f : A ⟶ B) : f ≫ norm B = norm A ≫ f
参数：f : A ⟶ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rep.hom_ext`：∀ {k : Type u} {G : Type v} [inst : Semiring k] [inst_1 : M
onoid G] {A B : Rep.{w, u, v} k G} {f g : A ⟶ B},   Rep.Hom.hom f = Rep.Hom.hom 
g…
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Representation.IntertwiningMap.instLinearMapClass`：∀ {A : Type u_1} {G :
 Type u_2} {V : Type u_3} {W : Type u_4} [inst : Semiring A] [inst_1 : Monoid G]
   [inst_2 : AddCommMonoid V] [inst_3 :…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Rep.hom_comm_apply`：hom_comm_apply (f : A ⟶ B) (g : G) (a : A) : f.hom (
A.ρ g a) = B.ρ g (f.hom a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma norm_comm {A B : Rep k G} (f : A ⟶ B) : f ≫ norm B = norm A ≫ f := by
  ext; simp [Representation.norm, hom_comm_apply]

/-- Given a representation `A` of a finite group `G`, the norm map `A ⟶ A` defined by
`x ↦ ∑ A.ρ g x` for `g` in `G` defines a natural endomorphism of the identity functor. -/
@[simps]
/-
**Rep.normNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：normNatTrans : End (𝟭 (Rep k G)) where app
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Rep.norm_comm`：norm_comm {A B : Rep k G} (f : A ⟶ B) : f ≫ norm B = norm
 A ≫ f

--- 原说明 ---
Given a representation `A` of a finite group `G`, the norm map `A ⟶ A` defined b
y
`x ↦ ∑ A.ρ g x` for `g` in `G` defines a natural endomorphism of the identity fu
nctor.
-/
def normNatTrans : End (𝟭 (Rep k G)) where
  app := norm
  naturality _ _ := norm_comm

end

noncomputable section Linearization

variable (k G)

noncomputable section Finsupp

open Finsupp

variable (α : Type u') (A : Rep k G)

variable {k G} in
/-- The representation on `α →₀ A` defined pointwise by a representation on `A`. -/
/-
**Rep.finsupp** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：finsupp : Rep k G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The representation on `α →₀ A` defined pointwise by a representation on `A`.
-/
abbrev finsupp : Rep k G :=
  Rep.of (Representation.finsupp A.ρ α)
/-
**Rep.finsupp_V** 是 Mathlib 中的一个定理，位于命名空间 `Rep`。
形式化陈述：∀ (k : Type u) (G : Type v) [inst : CommRing k] [inst_1 : Monoid G] (α : T
ype u') (A : Rep.{u_1, u, v} k G),   ↑(Rep.finsupp α A) = (α →₀ ↑A)
参数：k : Type u；G : Type v；α : Type u'；A : Rep.{u_1, u, v} k G；Rep.finsupp α A；α →
₀ ↑A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma finsupp_V : (finsupp α A).V = (α →₀ A.V) := rfl

/-- The representation on `α →₀ k[G]` defined pointwise by the left regular representation on
`k[G]`. -/
/-
**Rep.free** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：free : Rep k G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The representation on `α →₀ k[G]` defined pointwise by the left regular represen
tation on
`k[G]`.
-/
abbrev free : Rep k G := Rep.of (Representation.free k G α)

variable {α}

/-- Given `f : α → A`, the natural representation morphism `(α →₀ k[G]) ⟶ A` sending
`single a (single g r) ↦ r • A.ρ g (f a)`. -/
/-
**Rep.freeLift** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：freeLift (f : α -> A) : free k G α ⟶ A
参数：f : α -> A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : α → A`, the natural representation morphism `(α →₀ k[G]) ⟶ A` sending
`single a (single g r) ↦ r • A.ρ g (f a)`.
-/
abbrev freeLift (f : α → A) :
    free k G α ⟶ A := Rep.ofHom (Representation.freeLift A.ρ f)

variable (α) in
/-- The natural linear equivalence between functions `α → A` and representation morphisms
`(α →₀ k[G]) ⟶ A`. -/
/-
**Rep.freeLiftLEquiv** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：freeLiftLEquiv : (free k G α ⟶ A) ≃ₗ[k] (α -> A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural linear equivalence between functions `α → A` and representation morp
hisms
`(α →₀ k[G]) ⟶ A`.
-/
abbrev freeLiftLEquiv :
    (free k G α ⟶ A) ≃ₗ[k] (α → A) :=
  homLinearEquiv _ _ ≪≫ₗ Representation.freeLiftLEquiv A.ρ α
/-
**Rep.free_ext** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：free_ext (f g : free k G α ⟶ A) (h : forall i : α, f.hom (single i (.singl
e 1 1)) = g.hom (single i (.single 1 1))) : f = g
参数：f g : free k G α ⟶ A；h : forall i : α, f.hom (single i (.single 1 1)) = g.hom
 (single i (.single 1 1))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
-/
lemma free_ext (f g : free k G α ⟶ A)
    (h : ∀ i : α, f.hom (single i (.single 1 1)) = g.hom (single i (.single 1 1))) : f = g := by
  exact (freeLiftLEquiv k G α A).injective (funext_iff.2 h)

variable {A}
section

open MonoidalCategory

variable (A B : Rep.{u} k G) (α : Type u) [DecidableEq α]

open TensorProduct in
/-- Given representations `A, B` and a type `α`, this is the natural representation isomorphism
`(α →₀ A) ⊗ B ≅ (A ⊗ B) →₀ α` sending `single x a ⊗ₜ b ↦ single x (a ⊗ₜ b)`. -/
/-
**Rep.finsuppTensorLeft** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：finsuppTensorLeft : A.finsupp α otimes B ≅ (A otimes B).finsupp α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given representations `A, B` and a type `α`, this is the natural representation 
isomorphism
`(α →₀ A) ⊗ B ≅ (A ⊗ B) →₀ α` sending `single x a ⊗ₜ b ↦ single x (a ⊗ₜ b)`.
-/
abbrev finsuppTensorLeft : A.finsupp α ⊗ B ≅ (A ⊗ B).finsupp α :=
  mkIso (Representation.finsuppTensorLeft A.ρ B.ρ α)

/-- Given representations `A, B` and a type `α`, this is the natural representation isomorphism
`A ⊗ (α →₀ B) ≅ (A ⊗ B) →₀ α` sending `a ⊗ₜ single x b ↦ single x (a ⊗ₜ b)`. -/
/-
**Rep.finsuppTensorRight** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：finsuppTensorRight : A otimes B.finsupp α ≅ (A otimes B).finsupp α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given representations `A, B` and a type `α`, this is the natural representation 
isomorphism
`A ⊗ (α →₀ B) ≅ (A ⊗ B) →₀ α` sending `a ⊗ₜ single x b ↦ single x (a ⊗ₜ b)`.
-/
abbrev finsuppTensorRight : A ⊗ B.finsupp α ≅ (A ⊗ B).finsupp α :=
  mkIso (Representation.finsuppTensorRight A.ρ B.ρ α)

section

variable (k G α : Type u) [DecidableEq α] [CommRing k] [Monoid G]

/-- The natural isomorphism sending `single g r₁ ⊗ single a r₂ ↦ single a (single g r₁r₂)`. -/
/-
**Rep.leftRegularTensorTrivialIsoFree** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：leftRegularTensorTrivialIsoFree : leftRegular k G otimes trivial k G k[α] 
≅ free k G α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism sending `single g r₁ ⊗ single a r₂ ↦ single a (single g 
r₁r₂)`.
-/
abbrev leftRegularTensorTrivialIsoFree : leftRegular k G ⊗ trivial k G k[α] ≅ free k G α :=
  mkIso (Representation.leftRegularTensorTrivialIsoFree α)

end
end
end Finsupp

/-- The monoidal functor sending a type `H` with a `G`-action to the induced `k`-linear
`G`-representation on `k[H].` -/
@[simps]
/-
**Rep.linearization** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：linearization : Action (Type w) G ⥤ Rep.{max w u} k G where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoidal functor sending a type `H` with a `G`-action to the induced `k`-lin
ear
`G`-representation on `k[H].`
-/
abbrev linearization : Action (Type w) G ⥤ Rep.{max w u} k G where
  obj X := .of <| .linearize k G X
  map f := Rep.ofHom <| Representation.linearizeMap f

open MonoidalCategory Representation.LinearizeMonoidal in
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (linearization k G).LaxMonoidal where
  ε := ofHom (ε k G)
  μ X Y := ofHom (μ X Y)
  μ_natural_left f Z := hom_ext <| μ_comp_rTensor f Z
  μ_natural_right Z f := by ext1; simp [μ_comp_lTensor _]
  associativity X Y Z := by ext1; simp [μ_comp_assoc _]
  left_unitality X := hom_ext <| μ_leftUnitor X
  right_unitality X := hom_ext <| μ_rightUnitor X

open MonoidalCategory Representation.LinearizeMonoidal in
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (linearization k G).OplaxMonoidal where
  η := ofHom (η k G)
  δ X Y := ofHom (δ X Y)
  δ_natural_left f Z := hom_ext <| rTensor_comp_δ Z f
  δ_natural_right Z f := hom_ext <| lTensor_comp_δ Z f
  oplax_associativity X Y Z := hom_ext <| by simpa using assoc_comp_δ X Y Z (k := k)
  oplax_left_unitality X := hom_ext <| leftUnitor_δ X
  oplax_right_unitality X := hom_ext <| rightUnitor_δ X

open MonoidalCategory Representation.LinearizeMonoidal in
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (linearization k G).Monoidal where
  ε_η := hom_ext <| η_ε k G
  η_ε := hom_ext <| ε_η k G
  μ_δ X Y := hom_ext <| δ_μ (k := k) X Y
  δ_μ X Y := hom_ext <| μ_δ (k := k) X Y

variable {k G}

open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

open scoped MonoidalCategory

section

open MonoidalCategory Representation.LinearizeMonoidal

/-
**Rep.** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μ_def {X Y : Action (Type u) G} : Functor.LaxMonoidal.μ (linearization k G) X Y =
    ofHom (μ X Y) := rfl
/-
**Rep.** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μ_hom {X Y : Action (Type u) G} : (Functor.LaxMonoidal.μ (linearization k G) X Y).hom
    = μ X Y := rfl
/-
**Rep.** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ε_def : Functor.LaxMonoidal.ε (linearization k G) = ofHom (ε k G) := rfl
/-
**Rep.** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ε_hom : (Functor.LaxMonoidal.ε (linearization k G)).hom = ε k G := rfl
/-
**Rep.** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_def {X Y : Action (Type u) G} : Functor.OplaxMonoidal.δ (linearization k G) X Y =
    ofHom (δ X Y) := rfl
/-
**Rep.** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_hom {X Y : Action (Type u) G} : (Functor.OplaxMonoidal.δ (linearization k G) X Y).hom
    = δ X Y := rfl
/-
**Rep.** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma η_def : Functor.OplaxMonoidal.η (linearization k G) = ofHom (η k G) := rfl
/-
**Rep.** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma η_hom : (Functor.OplaxMonoidal.η (linearization k G)).hom = η k G := rfl

end

variable (k G) in
/-- The linearization of a type `X` on which `G` acts trivially is the trivial `G`-representation
on `k[X]`. -/
/-
**Rep.linearizationTrivialIso** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：linearizationTrivialIso (X : Type u) : (linearization k G).obj (Action.tri
vial _ X) ≅ trivial k G k[X]
参数：X : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linearization of a type `X` on which `G` acts trivially is the trivial `G`-r
epresentation
on `k[X]`.
-/
abbrev linearizationTrivialIso (X : Type u) :
    (linearization k G).obj (Action.trivial _ X) ≅ trivial k G k[X] :=
  Rep.mkIso (Representation.linearizeTrivialIso k G X)

variable (k G) in
/-- The linearization of a type `H` with a `G`-action is definitionally isomorphic to the
`k`-linear `G`-representation on `k[H]` induced by the `G`-action on `H`. -/
/-
**Rep.linearizationOfMulActionIso** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：linearizationOfMulActionIso (H : Type u) [MulAction G H] : (linearization 
k G).obj (Action.ofMulAction G H) ≅ ofMulAction k G H
参数：H : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linearization of a type `H` with a `G`-action is definitionally isomorphic t
o the
`k`-linear `G`-representation on `k[H]` induced by the `G`-action on `H`.
-/
abbrev linearizationOfMulActionIso (H : Type u) [MulAction G H] :
    (linearization k G).obj (Action.ofMulAction G H) ≅ ofMulAction k G H :=
  Rep.mkIso (Representation.linearizeOfMulActionIso k G H)

/-- Given a `k`-linear `G`-representation `A`, there is a `k`-linear isomorphism between
representation morphisms `Hom(k[G], A)` and `A`. -/
/-
**Rep.leftRegularHomEquiv** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：leftRegularHomEquiv (A : Rep k G) : (leftRegular k G ⟶ A) ≃ₗ[k] A
参数：A : Rep k G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `k`-linear `G`-representation `A`, there is a `k`-linear isomorphism bet
ween
representation morphisms `Hom(k[G], A)` and `A`.
-/
abbrev leftRegularHomEquiv (A : Rep k G) : (leftRegular k G ⟶ A) ≃ₗ[k] A :=
  homLinearEquiv _ _ ≪≫ₗ Representation.leftRegularMapEquiv A.ρ

set_option backward.isDefEq.respectTransparency.types false in
/-
**Rep.leftRegularHomEquiv_symm_single** 是 Mathlib 中的一个定理，位于命名空间 `Rep`。
形式化陈述：leftRegularHomEquiv_symm_single {A : Rep k G} (x : A) (g : G) : ((leftRegu
larHomEquiv A).symm x).hom (.single g 1) = A.ρ g x
参数：x : A；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `Representation.leftRegularMapEquiv_symm_apply_toFun`：∀ {G : Type v} [ins
t : Monoid G] {V : Type v'} [inst_1 : AddCommMonoid V] {k : Type u} [inst_2 : Co
mmSemiring k]   [inst_3 : _root_.Module k…
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem leftRegularHomEquiv_symm_single {A : Rep k G} (x : A) (g : G) :
    ((leftRegularHomEquiv A).symm x).hom (.single g 1) = A.ρ g x := by
  simp [homEquiv]

end Linearization

end

end Rep

