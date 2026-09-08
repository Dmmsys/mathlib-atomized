/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Adjunctions with a parameter

Given bifunctors `F : C₁ ⥤ C₂ ⥤ C₃` and `G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂`,
this file introduces the notation `F ⊣₂ G` for the adjunctions
with a parameter (in `C₁`) between `F` and `G`.

(See `MonoidalClosed.internalHomAdjunction₂` in the file
`CategoryTheory.Closed.Monoidal` for an example of such an adjunction.)

Note: this notion is weaker than the notion of
"adjunction of two variables" which appears in the mathematical literature.
In order to have an adjunction of two variables, we need
a third functor `H : C₂ᵒᵖ ⥤ C₃ ⥤ C₁` and two adjunctions with
a parameter `F ⊣₂ G` and `F.flip ⊣₂ H`.

## TODO

Show that given `F : C₁ ⥤ C₂ ⥤ C₃`, if `F.obj X₁` has a right adjoint
`G X₁ : C₃ ⥤ C₂` for any `X₁ : C₁`, then `G` extends as a
bifunctor `G' : C₁ᵒᵖ ⥤ C₃ ⥤ C₂` with `F ⊣₂ G'` (and similarly for
left adjoints).

## References
* https://ncatlab.org/nlab/show/two-variable+adjunction

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Opposite CategoryTheory.Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  (F : C₁ ⥤ C₂ ⥤ C₃) (G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂)

/-- Given bifunctors `F : C₁ ⥤ C₂ ⥤ C₃` and `G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂`,
an adjunction with parameter `F ⊣₂ G` consists of the data of
adjunctions `F.obj X₁ ⊣ G.obj (op X₁)` for all `X₁ : C₁` which
satisfy a naturality condition with respect to `X₁`. -/
/-
**CategoryTheory.ParametrizedAdjunction** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheor
y`。
形式化陈述：ParametrizedAdjunction where /-- a family of adjunctions -/ adj (X₁ : C₁) 
: F.obj X₁ ⊣ G.obj (op X₁) unit_whiskerRight_map {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) : (a
dj X₁).unit ≫ whiskerRight (F.map f) _ = (adj Y₁).unit ≫ whiskerLeft _ (G.map f.
op)
参数：X₁ : C₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given bifunctors `F : C₁ ⥤ C₂ ⥤ C₃` and `G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂`,
an adjunction with parameter `F ⊣₂ G` consists of the data of
adjunctions `F.obj X₁ ⊣ G.obj (op X₁)` for all `X₁ : C₁` which
satisfy a naturality condition with respect to `X₁`.
-/
structure ParametrizedAdjunction where
  /-- a family of adjunctions -/
  adj (X₁ : C₁) : F.obj X₁ ⊣ G.obj (op X₁)
  unit_whiskerRight_map {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) :
    (adj X₁).unit ≫ whiskerRight (F.map f) _ = (adj Y₁).unit ≫ whiskerLeft _ (G.map f.op) := by
      cat_disch

/-- The notation `F ⊣₂ G` stands for `ParametrizedAdjunction F G`
representing that the bifunctor `F` is the left adjoint to `G`
in an adjunction with a parameter. -/
infixl:15 " ⊣₂ " => ParametrizedAdjunction

namespace ParametrizedAdjunction

attribute [reassoc] unit_whiskerRight_map

variable {F G}

set_option backward.defeqAttrib.useBackward true in
/-- Alternative constructor for parametrized adjunctions, for which
the compatibility is stated in terms of `Adjunction.homEquiv`. -/
@[simps]
/-
**CategoryTheory.ParametrizedAdjunction.mk'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ParametrizedAdjunction`。
形式化陈述：mk' (adj : forall (X₁ : C₁), F.obj X₁ ⊣ G.obj (op X₁)) (h : forall {X₁ Y₁ 
: C₁} (f : X₁ ⟶ Y₁) {X₂ : C₂} {X₃ : C₃} (g : (F.obj Y₁).obj X₂ ⟶ X₃), (adj X₁).h
omEquiv X₂ X₃ ((F.map f).app X₂ ≫ g) = (adj Y₁).homEquiv X₂ X₃ g ≫ (G.map f.op).
app X₃
参数：adj : forall (X₁ : C₁), F.obj X₁ ⊣ G.obj (op X₁)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative constructor for parametrized adjunctions, for which
the compatibility is stated in terms of `Adjunction.homEquiv`.
-/
def mk' (adj : ∀ (X₁ : C₁), F.obj X₁ ⊣ G.obj (op X₁))
    (h : ∀ {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) {X₂ : C₂} {X₃ : C₃} (g : (F.obj Y₁).obj X₂ ⟶ X₃),
      (adj X₁).homEquiv X₂ X₃ ((F.map f).app X₂ ≫ g) =
        (adj Y₁).homEquiv X₂ X₃ g ≫ (G.map f.op).app X₃ := by cat_disch) :
    F ⊣₂ G where
  adj := adj
  unit_whiskerRight_map {X₁ Y₁} f := by
    ext X₂
    simpa [Adjunction.homEquiv_unit] using h f (X₂ := X₂) (𝟙 _)

variable (adj₂ : F ⊣₂ G)
  {X₁ Y₁ : C₁} {X₂ Y₂ : C₂} {X₃ Y₃ : C₃}

/-- The bijection `((F.obj X₁).obj X₂ ⟶ X₃) ≃ (X₂ ⟶ (G.obj (op X₁)).obj X₃)`
given by an adjunction with a parameter `adj₂ : F ⊣₂ G`. -/
/-
**CategoryTheory.ParametrizedAdjunction.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.ParametrizedAdjunction`。
形式化陈述：homEquiv : ((F.obj X₁).obj X₂ ⟶ X₃) ≃ (X₂ ⟶ (G.obj (op X₁)).obj X₃)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `((F.obj X₁).obj X₂ ⟶ X₃) ≃ (X₂ ⟶ (G.obj (op X₁)).obj X₃)`
given by an adjunction with a parameter `adj₂ : F ⊣₂ G`.
-/
def homEquiv : ((F.obj X₁).obj X₂ ⟶ X₃) ≃ (X₂ ⟶ (G.obj (op X₁)).obj X₃) :=
  (adj₂.adj X₁).homEquiv _ _
/-
**CategoryTheory.ParametrizedAdjunction.homEquiv_eq** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ParametrizedAdjunction`。
形式化陈述：homEquiv_eq : adj₂.homEquiv = (adj₂.adj X₁).homEquiv X₂ X₃
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homEquiv_eq : adj₂.homEquiv = (adj₂.adj X₁).homEquiv X₂ X₃ := rfl

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.ParametrizedAdjunction.homEquiv_naturality_one** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.ParametrizedAdjunction`。
形式化陈述：homEquiv_naturality_one (f₁ : X₁ ⟶ Y₁) (g : (F.obj Y₁).obj X₂ ⟶ X₃) : adj₂
.homEquiv ((F.map f₁).app X₂ ≫ g) = adj₂.homEquiv g ≫ (G.map f₁.op).app X₃
参数：f₁ : X₁ ⟶ Y₁；g : (F.obj Y₁).obj X₂ ⟶ X₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.ParametrizedAdjunction.unit_whiskerRight_map`：∀ {C₁ : Typ
e u₁} {C₂ : Type u₂} {C₃ : Type u₃} [inst : CategoryTheory.Category.{v₁, u₁} C₁]
   [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂]…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homEquiv_naturality_one (f₁ : X₁ ⟶ Y₁) (g : (F.obj Y₁).obj X₂ ⟶ X₃) :
    adj₂.homEquiv ((F.map f₁).app X₂ ≫ g) =
      adj₂.homEquiv g ≫ (G.map f₁.op).app X₃ := by
  have := NatTrans.congr_app (adj₂.unit_whiskerRight_map f₁) X₂
  dsimp at this
  simp only [homEquiv_eq, Adjunction.homEquiv_unit, Functor.comp_obj, Functor.map_comp,
    Category.assoc, NatTrans.naturality, reassoc_of% this]

@[reassoc]
/-
**CategoryTheory.ParametrizedAdjunction.homEquiv_naturality_two** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.ParametrizedAdjunction`。
形式化陈述：homEquiv_naturality_two (f₂ : X₂ ⟶ Y₂) (g : (F.obj X₁).obj Y₂ ⟶ X₃) : adj₂
.homEquiv ((F.obj X₁).map f₂ ≫ g) = f₂ ≫ adj₂.homEquiv g
参数：f₂ : X₂ ⟶ Y₂；g : (F.obj X₁).obj Y₂ ⟶ X₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_left`：homEquiv_naturality_
left (f : X' ⟶ X) (g : F.obj X ⟶ Y) : (adj.homEquiv X' Y) (F.map f ≫ g) = f ≫ (a
dj.homEquiv X Y) g
-/
lemma homEquiv_naturality_two (f₂ : X₂ ⟶ Y₂) (g : (F.obj X₁).obj Y₂ ⟶ X₃) :
    adj₂.homEquiv ((F.obj X₁).map f₂ ≫ g) = f₂ ≫ adj₂.homEquiv g :=
  (adj₂.adj X₁).homEquiv_naturality_left _ _

@[reassoc]
/-
**CategoryTheory.ParametrizedAdjunction.homEquiv_naturality_three** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.ParametrizedAdjunction`。
形式化陈述：homEquiv_naturality_three (f₃ : X₃ ⟶ Y₃) (g : (F.obj X₁).obj X₂ ⟶ X₃) : ad
j₂.homEquiv (g ≫ f₃) = adj₂.homEquiv g ≫ (G.obj (op X₁)).map f₃
参数：f₃ : X₃ ⟶ Y₃；g : (F.obj X₁).obj X₂ ⟶ X₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_right`：homEquiv_naturality
_right (f : F.obj X ⟶ Y) (g : Y ⟶ Y') : (adj.homEquiv X Y') (f ≫ g) = (adj.homEq
uiv X Y) f ≫ G.map g
-/
lemma homEquiv_naturality_three (f₃ : X₃ ⟶ Y₃) (g : (F.obj X₁).obj X₂ ⟶ X₃) :
    adj₂.homEquiv (g ≫ f₃) = adj₂.homEquiv g ≫ (G.obj (op X₁)).map f₃ :=
  (adj₂.adj X₁).homEquiv_naturality_right _ _

@[reassoc]
/-
**CategoryTheory.ParametrizedAdjunction.homEquiv_symm_naturality_one** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.ParametrizedAdjunction`。
形式化陈述：homEquiv_symm_naturality_one (f₁ : X₁ ⟶ Y₁) (g : X₂ ⟶ (G.obj (op Y₁)).obj 
X₃) : adj₂.homEquiv.symm (g ≫ (G.map f₁.op).app X₃) = (F.map f₁).app X₂ ≫ adj₂.h
omEquiv.symm g
参数：f₁ : X₁ ⟶ Y₁；g : X₂ ⟶ (G.obj (op Y₁)).obj X₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用引理 `CategoryTheory.ParametrizedAdjunction.homEquiv_naturality_one`：homEquiv_
naturality_one (f₁ : X₁ ⟶ Y₁) (g : (F.obj Y₁).obj X₂ ⟶ X₃) : adj₂.homEquiv ((F.m
ap f₁).app X₂ ≫ g) = adj₂.homEquiv g ≫ (G.map f₁.op…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homEquiv_symm_naturality_one
    (f₁ : X₁ ⟶ Y₁) (g : X₂ ⟶ (G.obj (op Y₁)).obj X₃) :
    adj₂.homEquiv.symm (g ≫ (G.map f₁.op).app X₃) =
      (F.map f₁).app X₂ ≫ adj₂.homEquiv.symm g :=
  adj₂.homEquiv.injective (by simp [homEquiv_naturality_one])

@[reassoc]
/-
**CategoryTheory.ParametrizedAdjunction.homEquiv_symm_naturality_two** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.ParametrizedAdjunction`。
形式化陈述：homEquiv_symm_naturality_two (f₂ : X₂ ⟶ Y₂) (g : Y₂ ⟶ (G.obj (op X₁)).obj 
X₃) : adj₂.homEquiv.symm (f₂ ≫ g) = (F.obj X₁).map f₂ ≫ adj₂.homEquiv.symm g
参数：f₂ : X₂ ⟶ Y₂；g : Y₂ ⟶ (G.obj (op X₁)).obj X₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用引理 `CategoryTheory.ParametrizedAdjunction.homEquiv_naturality_two`：homEquiv_
naturality_two (f₂ : X₂ ⟶ Y₂) (g : (F.obj X₁).obj Y₂ ⟶ X₃) : adj₂.homEquiv ((F.o
bj X₁).map f₂ ≫ g) = f₂ ≫ adj₂.homEquiv g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homEquiv_symm_naturality_two
    (f₂ : X₂ ⟶ Y₂) (g : Y₂ ⟶ (G.obj (op X₁)).obj X₃) :
    adj₂.homEquiv.symm (f₂ ≫ g) =
      (F.obj X₁).map f₂ ≫ adj₂.homEquiv.symm g :=
  adj₂.homEquiv.injective (by simp [homEquiv_naturality_two])

@[reassoc]
/-
**CategoryTheory.ParametrizedAdjunction.homEquiv_symm_naturality_three** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.ParametrizedAdjunction`。
形式化陈述：homEquiv_symm_naturality_three (f₃ : X₃ ⟶ Y₃) (g : X₂ ⟶ (G.obj (op X₁)).ob
j X₃) : adj₂.homEquiv.symm (g ≫ (G.obj (op X₁)).map f₃) = adj₂.homEquiv.symm g ≫
 f₃
参数：f₃ : X₃ ⟶ Y₃；g : X₂ ⟶ (G.obj (op X₁)).obj X₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用引理 `CategoryTheory.ParametrizedAdjunction.homEquiv_naturality_three`：homEqui
v_naturality_three (f₃ : X₃ ⟶ Y₃) (g : (F.obj X₁).obj X₂ ⟶ X₃) : adj₂.homEquiv (
g ≫ f₃) = adj₂.homEquiv g ≫ (G.obj (op X₁)).map f₃
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homEquiv_symm_naturality_three
    (f₃ : X₃ ⟶ Y₃) (g : X₂ ⟶ (G.obj (op X₁)).obj X₃) :
    adj₂.homEquiv.symm (g ≫ (G.obj (op X₁)).map f₃) =
      adj₂.homEquiv.symm g ≫ f₃ :=
  adj₂.homEquiv.injective (by simp [homEquiv_naturality_three])

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.ParametrizedAdjunction.whiskerLeft_map_counit** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.ParametrizedAdjunction`。
形式化陈述：whiskerLeft_map_counit {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) : whiskerLeft _ (F.map f
) ≫ (adj₂.adj Y₁).counit = whiskerRight (G.map f.op) _ ≫ (adj₂.adj X₁).counit
参数：f : X₁ ⟶ Y₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ParametrizedAdjunction.homEquiv_naturality_one`：homEquiv_
naturality_one (f₁ : X₁ ⟶ Y₁) (g : (F.obj Y₁).obj X₂ ⟶ X₃) : adj₂.homEquiv ((F.m
ap f₁).app X₂ ≫ g) = adj₂.homEquiv g ≫ (G.map f₁.op…
· 使用引理 `CategoryTheory.ParametrizedAdjunction.homEquiv_naturality_two`：homEquiv_
naturality_two (f₂ : X₂ ⟶ Y₂) (g : (F.obj X₁).obj Y₂ ⟶ X₃) : adj₂.homEquiv ((F.o
bj X₁).map f₂ ≫ g) = f₂ ≫ adj₂.homEquiv g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerLeft_map_counit {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) :
    whiskerLeft _ (F.map f) ≫ (adj₂.adj Y₁).counit =
      whiskerRight (G.map f.op) _ ≫ (adj₂.adj X₁).counit := by
  ext X₃
  dsimp
  apply adj₂.homEquiv.injective
  rw [homEquiv_naturality_one, homEquiv_naturality_two]
  simp [homEquiv_eq, Adjunction.homEquiv_unit]

end ParametrizedAdjunction

end CategoryTheory

