/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Category of preorders

This defines `Preord`, the category of preorders with monotone maps.
-/

@[expose] public section


universe u

open CategoryTheory

/-- The category of preorders. -/
/-
**Preord** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u_1 + 1)
参数：u_1 + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of preorders.
-/
structure Preord where
  /-- Construct a bundled `Preord` from the underlying type and typeclass. -/
  of ::
  /-- The underlying preordered type. -/
  (carrier : Type*)
  [str : Preorder carrier]

attribute [instance] Preord.str

initialize_simps_projections Preord (carrier → coe, -str)

namespace Preord

/-
**Preord.** 是 Mathlib 中的一个实例，位于命名空间 `Preord`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort Preord (Type u) :=
  ⟨Preord.carrier⟩

attribute [coe] Preord.carrier

/-- The type of morphisms in `Preord R`. -/
@[ext]
/-
**Preord.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `Preord`。
形式化陈述：Preord → Preord → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `Preord R`.
-/
structure Hom (X Y : Preord.{u}) where
  private mk ::
  /-- The underlying `OrderHom`. -/
  hom' : X →o Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Preord.** 是 Mathlib 中的一个实例，位于命名空间 `Preord`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category Preord.{u} where
  Hom X Y := Hom X Y
  id _ := ⟨OrderHom.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Preord.** 是 Mathlib 中的一个实例，位于命名空间 `Preord`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory Preord (· →o ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `Preord` back into a `OrderHom`. -/
/-
**Preord.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `Preord.Hom`。
形式化陈述：{X Y : Preord} → X.Hom Y → ↑X →o ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `Preord` back into a `OrderHom`.
-/
abbrev Hom.hom {X Y : Preord.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := Preord) f

/-- Typecheck a `OrderHom` as a morphism in `Preord`. -/
/-
**Preord.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `Preord`。
形式化陈述：ofHom {X Y : Type u} [Preorder X] [Preorder Y] (f : X ->o Y) : of X ⟶ of Y
参数：f : X ->o Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `OrderHom` as a morphism in `Preord`.
-/
abbrev ofHom {X Y : Type u} [Preorder X] [Preorder Y] (f : X →o Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := Preord) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**Preord.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `Preord.Hom.Simps`。
形式化陈述：(X Y : Preord) → X.Hom Y → ↑X →o ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (X Y : Preord.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

/-
**Preord.coe_id** 是 Mathlib 中的一个引理，位于命名空间 `Preord`。
形式化陈述：coe_id {X : Preord} : (𝟙 X : X -> X) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma coe_id {X : Preord} : (𝟙 X : X → X) = id := rfl
/-
**Preord.coe_comp** 是 Mathlib 中的一个引理，位于命名空间 `Preord`。
形式化陈述：coe_comp {X Y Z : Preord} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g ∘
 f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comp {X Y Z : Preord} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[deprecated (since := "2026-02-15")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[ext]
/-
**Preord.ext** 是 Mathlib 中的一个引理，位于命名空间 `Preord`。
形式化陈述：ext {X Y : Preord} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g
参数：w : forall x : X, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
-/
lemma ext {X Y : Preord} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
/-
**Preord.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `Preord`。
形式化陈述：coe_of (X : Type u) [Preorder X] : (Preord.of X : Type u) = X
参数：X : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (X : Type u) [Preorder X] : (Preord.of X : Type u) = X := rfl

@[simp]
/-
**Preord.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `Preord`。
形式化陈述：hom_id {X : Preord} : (𝟙 X : X ⟶ X).hom = OrderHom.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_id {X : Preord} : (𝟙 X : X ⟶ X).hom = OrderHom.id := rfl

/- Provided for rewriting. -/
/-
**Preord.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `Preord`。
形式化陈述：id_apply (X : Preord) (x : X) : (𝟙 X : X ⟶ X) x = x
参数：X : Preord；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OrderHom.id_coe`：∀ {α : Type u_2} [inst : Preorder α], ⇑OrderHom.id = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (X : Preord) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/-
**Preord.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `Preord`。
形式化陈述：hom_comp {X Y Z : Preord} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = g.hom.co
mp f.hom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {X Y Z : Preord} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
/-
**Preord.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `Preord`。
形式化陈述：comp_apply {X Y Z : Preord} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = 
g (f x)
参数：f : X ⟶ Y；g : Y ⟶ Z；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OrderHom.comp_coe`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ]   (g : β →o γ) (f : α 
→o β), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {X Y Z : Preord} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/-
**Preord.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `Preord`。
形式化陈述：hom_ext {X Y : Preord} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Preord.Hom.ext`：∀ {X Y : Preord} {x y : X.Hom Y}, x.hom' = y.hom' → x = 
y
-/
lemma hom_ext {X Y : Preord} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/-
**Preord.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `Preord`。
形式化陈述：hom_ofHom {X Y : Type u} [Preorder X] [Preorder Y] (f : X ->o Y) : (ofHom 
f).hom = f
参数：f : X ->o Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {X Y : Type u} [Preorder X] [Preorder Y] (f : X →o Y) : (ofHom f).hom = f := rfl

@[simp]
/-
**Preord.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `Preord`。
形式化陈述：ofHom_hom {X Y : Preord} (f : X ⟶ Y) : ofHom (Hom.hom f) = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {X Y : Preord} (f : X ⟶ Y) : ofHom (Hom.hom f) = f := rfl

@[simp]
/-
**Preord.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `Preord`。
形式化陈述：ofHom_id {X : Type u} [Preorder X] : ofHom OrderHom.id = 𝟙 (of X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {X : Type u} [Preorder X] : ofHom OrderHom.id = 𝟙 (of X) := rfl

@[simp]
/-
**Preord.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `Preord`。
形式化陈述：ofHom_comp {X Y Z : Type u} [Preorder X] [Preorder Y] [Preorder Z] (f : X 
->o Y) (g : Y ->o Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g
参数：f : X ->o Y；g : Y ->o Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {X Y Z : Type u} [Preorder X] [Preorder Y] [Preorder Z]
    (f : X →o Y) (g : Y →o Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl
/-
**Preord.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Preord`。
形式化陈述：ofHom_apply {X Y : Type u} [Preorder X] [Preorder Y] (f : X ->o Y) (x : X)
 : (ofHom f) x = f x
参数：f : X ->o Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {X Y : Type u} [Preorder X] [Preorder Y] (f : X →o Y) (x : X) :
    (ofHom f) x = f x := rfl
/-
**Preord.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Preord`。
形式化陈述：inv_hom_apply {X Y : Preord} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x
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
lemma inv_hom_apply {X Y : Preord} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp
/-
**Preord.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Preord`。
形式化陈述：hom_inv_apply {X Y : Preord} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s
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
lemma hom_inv_apply {X Y : Preord} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp
/-
**Preord.** 是 Mathlib 中的一个实例，位于命名空间 `Preord`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited Preord :=
  ⟨of PUnit⟩

/-- Constructs an equivalence between preorders from an order isomorphism between them. -/
@[simps]
/-
**Preord.Iso.mk** 是 Mathlib 中的一个定义，位于命名空间 `Preord.Iso`。
形式化陈述：{α β : Preord} → ↑α ≃o ↑β → (α ≅ β)
参数：α ≅ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs an equivalence between preorders from an order isomorphism between th
em.
-/
def Iso.mk {α β : Preord.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
/-
**Preord.dual** 是 Mathlib 中的一个定义，位于命名空间 `Preord`。
形式化陈述：dual : Preord ⥤ Preord where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrderDual` as a functor.
-/
def dual : Preord ⥤ Preord where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `Preord` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/-
**Preord.dualEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Preord`。
形式化陈述：dualEquiv : Preord ≌ Preord where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `Preord` and itself induced by `OrderDual` both ways.
-/
def dualEquiv : Preord ≌ Preord where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

end Preord

/-- The embedding of `Preord` into `Cat`.
-/
@[simps]
/-
**preordToCat** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：preordToCat : Preord.{u} ⥤ Cat where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding of `Preord` into `Cat`.
-/
def preordToCat : Preord.{u} ⥤ Cat where
  obj X := .of X.1
  map f := f.hom.monotone.functor.toCatHom
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : preordToCat.{u}.Faithful where
  map_injective h := by ext x; exact Functor.congr_obj congr(($h).toFunctor) x
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : preordToCat.{u}.Full where
  map_surjective {X Y} f := ⟨⟨f.toFunctor.obj,
    @CategoryTheory.Functor.monotone X Y _ _ f.toFunctor⟩, rfl⟩
