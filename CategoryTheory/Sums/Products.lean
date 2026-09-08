/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Sums.Associator
public import Mathlib.CategoryTheory.Products.Associator

/-!
# Functors out of sums of categories.

This file records the universal property of sums of categories as an equivalence of
categories `Sum.functorEquiv : A ⊕ A' ⥤ B ≌ (A ⥤ B) × (A' ⥤ B)`, and characterizes its
precompositions with the left and right inclusion as corresponding to the projections on
the product side.

-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor

open scoped CategoryTheory.Prod

universe v u

variable (A : Type*) [Category* A] (A' : Type*) [Category* A']
  (B : Type u) [Category.{v} B]

namespace Sum

set_option backward.defeqAttrib.useBackward true in
/-- The equivalence between functors from a sum and the product of the functor categories. -/
@[simps]
/-
**CategoryTheory.Sum.functorEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sum`
。
形式化陈述：functorEquiv : A oplus A' ⥤ B ≌ (A ⥤ B) × (A' ⥤ B) where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between functors from a sum and the product of the functor categ
ories.
-/
def functorEquiv : A ⊕ A' ⥤ B ≌ (A ⥤ B) × (A' ⥤ B) where
  functor :=
    { obj F := ⟨inl_ A A' ⋙ F, inr_ A A' ⋙ F⟩
      map η := whiskerLeft (inl_ A A') η ×ₘ whiskerLeft (inr_ A A') η }
  inverse :=
    { obj F := Functor.sum' F.1 F.2
      map η := NatTrans.sum' η.1 η.2 }
  unitIso := NatIso.ofComponents <| fun F ↦ F.isoSum
  counitIso := NatIso.ofComponents (fun F ↦
    (Functor.inlCompSum' _ _).prod (Functor.inrCompSum' _ _) ≪≫ prod.etaIso F)

variable {A A' B}

@[simp]
/-
**CategoryTheory.Sum.functorEquiv_unit_app_app_inl** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Sum`。
形式化陈述：functorEquiv_unit_app_app_inl (X : A oplus A' ⥤ B) (a : A) : ((functorEqui
v A A' B).unit.app X).app (.inl a) = 𝟙 (X.obj (.inl a))
参数：X : A oplus A' ⥤ B；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma functorEquiv_unit_app_app_inl (X : A ⊕ A' ⥤ B) (a : A) :
    ((functorEquiv A A' B).unit.app X).app (.inl a) = 𝟙 (X.obj (.inl a)) :=
  rfl

@[simp]
/-
**CategoryTheory.Sum.functorEquiv_unit_app_app_inr** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Sum`。
形式化陈述：functorEquiv_unit_app_app_inr (X : A oplus A' ⥤ B) (a' : A') : ((functorEq
uiv A A' B).unit.app X).app (.inr a') = 𝟙 (X.obj (.inr a'))
参数：X : A oplus A' ⥤ B；a' : A'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma functorEquiv_unit_app_app_inr (X : A ⊕ A' ⥤ B) (a' : A') :
    ((functorEquiv A A' B).unit.app X).app (.inr a') = 𝟙 (X.obj (.inr a')) :=
  rfl

@[simp]
/-
**CategoryTheory.Sum.functorEquiv_unitIso_inv_app_app_inl** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Sum`。
形式化陈述：functorEquiv_unitIso_inv_app_app_inl (X : A oplus A' ⥤ B) (a : A) : ((func
torEquiv A A' B).unitIso.inv.app X).app (.inl a) = 𝟙 (X.obj (.inl a))
参数：X : A oplus A' ⥤ B；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma functorEquiv_unitIso_inv_app_app_inl (X : A ⊕ A' ⥤ B) (a : A) :
    ((functorEquiv A A' B).unitIso.inv.app X).app (.inl a) = 𝟙 (X.obj (.inl a)) :=
  rfl

@[simp]
/-
**CategoryTheory.Sum.functorEquiv_unitIso_inv_app_app_inr** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Sum`。
形式化陈述：functorEquiv_unitIso_inv_app_app_inr (X : A oplus A' ⥤ B) (a' : A') : ((fu
nctorEquiv A A' B).unitIso.inv.app X).app (.inr a') = 𝟙 (X.obj (.inr a'))
参数：X : A oplus A' ⥤ B；a' : A'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma functorEquiv_unitIso_inv_app_app_inr (X : A ⊕ A' ⥤ B) (a' : A') :
    ((functorEquiv A A' B).unitIso.inv.app X).app (.inr a') = 𝟙 (X.obj (.inr a')) :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- Composing the forward direction of `functorEquiv` with the first projection is the same as
precomposition with `inl_ A A'`. -/
@[simps!]
/-
**CategoryTheory.Sum.functorEquivFunctorCompFstIso** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Sum`。
形式化陈述：functorEquivFunctorCompFstIso : (functorEquiv A A' B).functor ⋙ Prod.fst (
A ⥤ B) (A' ⥤ B) ≅ (whiskeringLeft A (A oplus A') B).obj (inl_ A A')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing the forward direction of `functorEquiv` with the first projection is t
he same as
precomposition with `inl_ A A'`.
-/
def functorEquivFunctorCompFstIso :
    (functorEquiv A A' B).functor ⋙ Prod.fst (A ⥤ B) (A' ⥤ B) ≅
    (whiskeringLeft A (A ⊕ A') B).obj (inl_ A A') :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/-- Composing the forward direction of `functorEquiv` with the second projection is the same as
precomposition with `inr_ A A'`. -/
@[simps!]
/-
**CategoryTheory.Sum.functorEquivFunctorCompSndIso** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Sum`。
形式化陈述：functorEquivFunctorCompSndIso : (functorEquiv A A' B).functor ⋙ Prod.snd (
A ⥤ B) (A' ⥤ B) ≅ (whiskeringLeft A' (A oplus A') B).obj (inr_ A A')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing the forward direction of `functorEquiv` with the second projection is 
the same as
precomposition with `inr_ A A'`.
-/
def functorEquivFunctorCompSndIso :
    (functorEquiv A A' B).functor ⋙ Prod.snd (A ⥤ B) (A' ⥤ B) ≅
    (whiskeringLeft A' (A ⊕ A') B).obj (inr_ A A') :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/-- Composing the backward direction of `functorEquiv` with precomposition with `inl_ A A'`.
is naturally isomorphic to the first projection. -/
@[simps!]
/-
**CategoryTheory.Sum.functorEquivInverseCompWhiskeringLeftInlIso** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Sum`。
形式化陈述：functorEquivInverseCompWhiskeringLeftInlIso : (functorEquiv A A' B).invers
e ⋙ (whiskeringLeft A (A oplus A') B).obj (inl_ A A') ≅ Prod.fst (A ⥤ B) (A' ⥤ B
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing the backward direction of `functorEquiv` with precomposition with `inl
_ A A'`.
is naturally isomorphic to the first projection.
-/
def functorEquivInverseCompWhiskeringLeftInlIso :
    (functorEquiv A A' B).inverse ⋙ (whiskeringLeft A (A ⊕ A') B).obj (inl_ A A') ≅
    Prod.fst (A ⥤ B) (A' ⥤ B) :=
  NatIso.ofComponents (fun _ ↦ Functor.inlCompSum' _ _)

set_option backward.defeqAttrib.useBackward true in
/-- Composing the backward direction of `functorEquiv` with the second projection is the same as
precomposition with `inr_ A A'`. -/
@[simps!]
/-
**CategoryTheory.Sum.functorEquivInverseCompWhiskeringLeftInrIso** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Sum`。
形式化陈述：functorEquivInverseCompWhiskeringLeftInrIso : (functorEquiv A A' B).invers
e ⋙ (whiskeringLeft A' (A oplus A') B).obj (inr_ A A') ≅ Prod.snd (A ⥤ B) (A' ⥤ 
B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing the backward direction of `functorEquiv` with the second projection is
 the same as
precomposition with `inr_ A A'`.
-/
def functorEquivInverseCompWhiskeringLeftInrIso :
    (functorEquiv A A' B).inverse ⋙ (whiskeringLeft A' (A ⊕ A') B).obj (inr_ A A') ≅
    Prod.snd (A ⥤ B) (A' ⥤ B) :=
  NatIso.ofComponents (fun _ ↦ Functor.inrCompSum' _ _)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- A consequence of `functorEquiv`: we can construct a natural transformation of functors
`A ⊕ A' ⥤ B` from the data of natural transformations of their whiskering with `inl_` and `inr_`. -/
@[simps!]
/-
**CategoryTheory.Sum.natTransOfWhiskerLeftInlInr** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Sum`。
形式化陈述：natTransOfWhiskerLeftInlInr {F G : A oplus A' ⥤ B} (η₁ : Sum.inl_ A A' ⋙ F
 ⟶ Sum.inl_ A A' ⋙ G) (η₂ : Sum.inr_ A A' ⋙ F ⟶ Sum.inr_ A A' ⋙ G) : F ⟶ G
参数：η₁ : Sum.inl_ A A' ⋙ F ⟶ Sum.inl_ A A' ⋙ G；η₂ : Sum.inr_ A A' ⋙ F ⟶ Sum.inr_ 
A A' ⋙ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A consequence of `functorEquiv`: we can construct a natural transformation of fu
nctors
`A ⊕ A' ⥤ B` from the data of natural transformations of their whiskering with `
inl_` and `inr_`.
-/
def natTransOfWhiskerLeftInlInr {F G : A ⊕ A' ⥤ B}
    (η₁ : Sum.inl_ A A' ⋙ F ⟶ Sum.inl_ A A' ⋙ G) (η₂ : Sum.inr_ A A' ⋙ F ⟶ Sum.inr_ A A' ⋙ G) :
    F ⟶ G :=
  (Sum.functorEquiv A A' B).unit.app F ≫
    (Sum.functorEquiv A A' B).inverse.map ((η₁, η₂) :) ≫
      (Sum.functorEquiv A A' B).unitInv.app G

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Sum.natTransOfWhiskerLeftInlInr_id** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Sum`。
形式化陈述：natTransOfWhiskerLeftInlInr_id {F : A oplus A' ⥤ B} : natTransOfWhiskerLef
tInlInr (𝟙 (Sum.inl_ A A' ⋙ F)) (𝟙 (Sum.inr_ A A' ⋙ F)) = 𝟙 F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma natTransOfWhiskerLeftInlInr_id {F : A ⊕ A' ⥤ B} :
    natTransOfWhiskerLeftInlInr (𝟙 (Sum.inl_ A A' ⋙ F)) (𝟙 (Sum.inr_ A A' ⋙ F)) = 𝟙 F := by
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Sum.natTransOfWhiskerLeftInlInr_comp** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Sum`。
形式化陈述：natTransOfWhiskerLeftInlInr_comp {F G H : A oplus A' ⥤ B} (η₁ : Sum.inl_ A
 A' ⋙ F ⟶ Sum.inl_ A A' ⋙ G) (η₂ : Sum.inr_ A A' ⋙ F ⟶ Sum.inr_ A A' ⋙ G) (ν₁ : 
Sum.inl_ A A' ⋙ G ⟶ Sum.inl_ A A' ⋙ H) (ν₂ : Sum.inr_ A A' ⋙ G ⟶ Sum.inr_ A A' ⋙
 H) : natTransOfWhiskerLeftInlInr (η₁ ≫ ν₁) (η₂ ≫ ν₂) = natTransOfWhiskerLeftInl
Inr η₁ η₂ ≫ natTransOfWhiskerLeftInlInr ν₁ ν₂
参数：η₁ : Sum.inl_ A A' ⋙ F ⟶ Sum.inl_ A A' ⋙ G；η₂ : Sum.inr_ A A' ⋙ F ⟶ Sum.inr_ 
A A' ⋙ G；ν₁ : Sum.inl_ A A' ⋙ G ⟶ Sum.inl_ A A' ⋙ H；ν₂ : Sum.inr_ A A' ⋙ G ⟶ Sum
.inr_ A A' ⋙ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma natTransOfWhiskerLeftInlInr_comp {F G H : A ⊕ A' ⥤ B}
    (η₁ : Sum.inl_ A A' ⋙ F ⟶ Sum.inl_ A A' ⋙ G) (η₂ : Sum.inr_ A A' ⋙ F ⟶ Sum.inr_ A A' ⋙ G)
    (ν₁ : Sum.inl_ A A' ⋙ G ⟶ Sum.inl_ A A' ⋙ H) (ν₂ : Sum.inr_ A A' ⋙ G ⟶ Sum.inr_ A A' ⋙ H) :
    natTransOfWhiskerLeftInlInr (η₁ ≫ ν₁) (η₂ ≫ ν₂) = natTransOfWhiskerLeftInlInr η₁ η₂ ≫
      natTransOfWhiskerLeftInlInr ν₁ ν₂ := by
  cat_disch

set_option backward.isDefEq.respectTransparency false in
/-- A consequence of `functorEquiv`: we can construct a natural isomorphism of functors
`A ⊕ A' ⥤ B` from the data of natural isomorphisms of their whiskering with `inl_` and `inr_`. -/
@[simps]
/-
**CategoryTheory.Sum.natIsoOfWhiskerLeftInlInr** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Sum`。
形式化陈述：natIsoOfWhiskerLeftInlInr {F G : A oplus A' ⥤ B} (η₁ : Sum.inl_ A A' ⋙ F ≅
 Sum.inl_ A A' ⋙ G) (η₂ : Sum.inr_ A A' ⋙ F ≅ Sum.inr_ A A' ⋙ G) : F ≅ G where h
om
参数：η₁ : Sum.inl_ A A' ⋙ F ≅ Sum.inl_ A A' ⋙ G；η₂ : Sum.inr_ A A' ⋙ F ≅ Sum.inr_ 
A A' ⋙ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A consequence of `functorEquiv`: we can construct a natural isomorphism of funct
ors
`A ⊕ A' ⥤ B` from the data of natural isomorphisms of their whiskering with `inl
_` and `inr_`.
-/
def natIsoOfWhiskerLeftInlInr {F G : A ⊕ A' ⥤ B}
    (η₁ : Sum.inl_ A A' ⋙ F ≅ Sum.inl_ A A' ⋙ G) (η₂ : Sum.inr_ A A' ⋙ F ≅ Sum.inr_ A A' ⋙ G) :
    F ≅ G where
  hom := natTransOfWhiskerLeftInlInr η₁.hom η₂.hom
  inv := natTransOfWhiskerLeftInlInr η₁.inv η₂.inv
/-
**CategoryTheory.Sum.natIsoOfWhiskerLeftInlInr_eq** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Sum`。
形式化陈述：natIsoOfWhiskerLeftInlInr_eq {F G : A oplus A' ⥤ B} (η₁ : Sum.inl_ A A' ⋙ 
F ≅ Sum.inl_ A A' ⋙ G) (η₂ : Sum.inr_ A A' ⋙ F ≅ Sum.inr_ A A' ⋙ G) : natIsoOfWh
iskerLeftInlInr η₁ η₂ = (Sum.functorEquiv A A' B).unitIso.app _ ≪≫ (Sum.functorE
quiv A A' B).inverse.mapIso (Iso.prod η₁ η₂) ≪≫ (Sum.functorEquiv A A' B).unitIs
o.symm.app _
参数：η₁ : Sum.inl_ A A' ⋙ F ≅ Sum.inl_ A A' ⋙ G；η₂ : Sum.inr_ A A' ⋙ F ≅ Sum.inr_ 
A A' ⋙ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Sum.functorEquiv_unitIso`：∀ (A : Type u_1) [inst : Catego
ryTheory.Category.{v_1, u_1} A] (A' : Type u_2)   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_2} A'] (B : Type …
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Sum.natIsoOfWhiskerLeftInlInr_hom`：∀ {A : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} A] {A' : Type u_2}   [inst_1 : CategoryThe
ory.Category.{v_2, u_2} A'] {B : Type …
· 使用定理 `CategoryTheory.Sum.natTransOfWhiskerLeftInlInr_app`：∀ {A : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} A] {A' : Type u_2}   [inst_1 : CategoryT
heory.Category.{v_2, u_2} A'] {B : Type …
-/
lemma natIsoOfWhiskerLeftInlInr_eq {F G : A ⊕ A' ⥤ B}
    (η₁ : Sum.inl_ A A' ⋙ F ≅ Sum.inl_ A A' ⋙ G) (η₂ : Sum.inr_ A A' ⋙ F ≅ Sum.inr_ A A' ⋙ G) :
    natIsoOfWhiskerLeftInlInr η₁ η₂ =
    (Sum.functorEquiv A A' B).unitIso.app _ ≪≫
      (Sum.functorEquiv A A' B).inverse.mapIso (Iso.prod η₁ η₂) ≪≫
      (Sum.functorEquiv A A' B).unitIso.symm.app _ := by
  cat_disch

namespace Swap

set_option backward.defeqAttrib.useBackward true in
/-- `functorEquiv A A' B` transforms `Swap.equivalence` into `Prod.braiding`. -/
@[simps! hom_app_fst hom_app_snd inv_app_fst inv_app_snd]
/-
**CategoryTheory.Sum.Swap.equivalenceFunctorEquivFunctorIso** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Sum.Swap`。
形式化陈述：equivalenceFunctorEquivFunctorIso : ((equivalence A A').congrLeft.trans <|
 functorEquiv A' A B).functor ≅ ((functorEquiv A A' B).trans <| Prod.braiding (A
 ⥤ B) (A' ⥤ B)).functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`functorEquiv A A' B` transforms `Swap.equivalence` into `Prod.braiding`.
-/
def equivalenceFunctorEquivFunctorIso :
    ((equivalence A A').congrLeft.trans <| functorEquiv A' A B).functor ≅
      ((functorEquiv A A' B).trans <| Prod.braiding (A ⥤ B) (A' ⥤ B)).functor :=
  NatIso.ofComponents (fun E ↦
    Iso.prod
      ((Functor.associator _ _ E).symm ≪≫ isoWhiskerRight (Sum.swapCompInl A' A) _)
      ((Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (Sum.swapCompInr A' A) _))

end Swap

section CompatibilityWithProductAssociator

variable (T : Type*) [Category* T]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence `Sum.functorEquiv` sends associativity of sums to associativity of products -/
@[simps! hom_app_fst hom_app_snd_fst hom_app_snd_snd inv_app_fst inv_app_snd_fst inv_app_snd_snd]
/-
**CategoryTheory.Sum.associativityFunctorEquivNaturalityFunctorIso** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.Sum`。
形式化陈述：associativityFunctorEquivNaturalityFunctorIso : ((sum.associativity A A' T
).congrLeft.trans <| (Sum.functorEquiv A (A' oplus T) B).trans <| Equivalence.re
fl.prod Sum.functorEquiv _ _ B).functor ≅ (Sum.functorEquiv (A oplus A') T B).tr
ans .trans ((Sum.functorEquiv A A' B).prod Equivalence.refl) .functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `Sum.functorEquiv` sends associativity of sums to associativity 
of products
-/
def associativityFunctorEquivNaturalityFunctorIso :
    ((sum.associativity A A' T).congrLeft.trans <| (Sum.functorEquiv A (A' ⊕ T) B).trans <|
      Equivalence.refl.prod <| Sum.functorEquiv _ _ B).functor ≅
        (Sum.functorEquiv (A ⊕ A') T B).trans
          ((Sum.functorEquiv A A' B).prod Equivalence.refl) |>.trans
            (prod.associativity _ _ _) |>.functor :=
  NatIso.ofComponents (fun E ↦ Iso.prod
    ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (sum.inlCompInverseAssociator A A' T) E ≪≫ Functor.associator _ _ _)
    (Iso.prod
      (isoWhiskerLeft _ (Functor.associator _ _ E).symm ≪≫ (Functor.associator _ _ E).symm ≪≫
        isoWhiskerRight (sum.inlCompInrCompInverseAssociator A A' T) E ≪≫ Functor.associator _ _ E)
      (isoWhiskerLeft _ (Functor.associator _ _ E).symm ≪≫ (Functor.associator _ _ E).symm ≪≫
        isoWhiskerRight (sum.inrCompInrCompInverseAssociator A A' T) E))) (by
      intros
      ext
      all_goals
        dsimp
        simp only [Category.comp_id, Category.id_comp, NatTrans.naturality])

end CompatibilityWithProductAssociator

end Sum

end CategoryTheory

