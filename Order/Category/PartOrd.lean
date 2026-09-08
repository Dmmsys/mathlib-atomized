/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.Category.Preord
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Category of partial orders

This defines `PartOrd`, the category of partial orders with monotone maps.
-/

@[expose] public section

open CategoryTheory

universe v u

/-- The category of partial orders. -/
/-
**PartOrd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u_1 + 1)
参数：u_1 + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of partial orders.
-/
structure PartOrd where
  /-- Construct a bundled `PartOrd` from the underlying type and typeclass. -/
  of ::
  /-- The underlying partially ordered type. -/
  (carrier : Type*)
  [str : PartialOrder carrier]

attribute [instance] PartOrd.str

initialize_simps_projections PartOrd (carrier → coe, -str)

namespace PartOrd

/-
**PartOrd.** 是 Mathlib 中的一个实例，位于命名空间 `PartOrd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort PartOrd (Type _) :=
  ⟨PartOrd.carrier⟩

attribute [coe] PartOrd.carrier

/-- The type of morphisms in `PartOrd R`. -/
@[ext]
/-
**PartOrd.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `PartOrd`。
形式化陈述：PartOrd → PartOrd → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `PartOrd R`.
-/
structure Hom (X Y : PartOrd.{u}) where
  private mk ::
  /-- The underlying `OrderHom`. -/
  hom' : X →o Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**PartOrd.** 是 Mathlib 中的一个实例，位于命名空间 `PartOrd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category PartOrd.{u} where
  Hom X Y := Hom X Y
  id _ := ⟨OrderHom.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**PartOrd.** 是 Mathlib 中的一个实例，位于命名空间 `PartOrd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory PartOrd (· →o ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `PartOrd` back into a `OrderHom`. -/
/-
**PartOrd.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `PartOrd.Hom`。
形式化陈述：{X Y : PartOrd} → X.Hom Y → ↑X →o ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `PartOrd` back into a `OrderHom`.
-/
abbrev Hom.hom {X Y : PartOrd.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := PartOrd) f

/-- Typecheck a `OrderHom` as a morphism in `PartOrd`. -/
/-
**PartOrd.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `PartOrd`。
形式化陈述：ofHom {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ->o Y) : of 
X ⟶ of Y
参数：f : X ->o Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `OrderHom` as a morphism in `PartOrd`.
-/
abbrev ofHom {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X →o Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := PartOrd) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**PartOrd.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `PartOrd.Hom.Simps`。
形式化陈述：(X Y : PartOrd) → X.Hom Y → ↑X →o ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (X Y : PartOrd.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

/-
**PartOrd.coe_id** 是 Mathlib 中的一个引理，位于命名空间 `PartOrd`。
形式化陈述：coe_id {X : PartOrd} : (𝟙 X : X -> X) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma coe_id {X : PartOrd} : (𝟙 X : X → X) = id := rfl
/-
**PartOrd.coe_comp** 是 Mathlib 中的一个引理，位于命名空间 `PartOrd`。
形式化陈述：coe_comp {X Y Z : PartOrd} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g 
∘ f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comp {X Y Z : PartOrd} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[deprecated (since := "2026-02-16")] alias forget_map := ConcreteCategory.forget_map_eq_ofHom

@[ext]
/-
**PartOrd.ext** 是 Mathlib 中的一个引理，位于命名空间 `PartOrd`。
形式化陈述：ext {X Y : PartOrd} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g
参数：w : forall x : X, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
-/
lemma ext {X Y : PartOrd} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
/-
**PartOrd.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `PartOrd`。
形式化陈述：coe_of (X : Type u) [PartialOrder X] : (PartOrd.of X : Type u) = X
参数：X : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (X : Type u) [PartialOrder X] : (PartOrd.of X : Type u) = X := rfl

@[simp]
/-
**PartOrd.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `PartOrd`。
形式化陈述：hom_id {X : PartOrd} : (𝟙 X : X ⟶ X).hom = OrderHom.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_id {X : PartOrd} : (𝟙 X : X ⟶ X).hom = OrderHom.id := rfl

/- Provided for rewriting. -/
/-
**PartOrd.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `PartOrd`。
形式化陈述：id_apply (X : PartOrd) (x : X) : (𝟙 X : X ⟶ X) x = x
参数：X : PartOrd；x : X。
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
lemma id_apply (X : PartOrd) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/-
**PartOrd.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `PartOrd`。
形式化陈述：hom_comp {X Y Z : PartOrd} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = g.hom.c
omp f.hom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {X Y Z : PartOrd} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
/-
**PartOrd.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `PartOrd`。
形式化陈述：comp_apply {X Y Z : PartOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x =
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
lemma comp_apply {X Y Z : PartOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/-
**PartOrd.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `PartOrd`。
形式化陈述：hom_ext {X Y : PartOrd} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartOrd.Hom.ext`：∀ {X Y : PartOrd} {x y : X.Hom Y}, x.hom' = y.hom' → x 
= y
-/
lemma hom_ext {X Y : PartOrd} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/-
**PartOrd.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `PartOrd`。
形式化陈述：hom_ofHom {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ->o Y) :
 (ofHom f).hom = f
参数：f : X ->o Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X →o Y) : (ofHom f).hom = f :=
  rfl

@[simp]
/-
**PartOrd.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `PartOrd`。
形式化陈述：ofHom_hom {X Y : PartOrd} (f : X ⟶ Y) : ofHom (Hom.hom f) = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {X Y : PartOrd} (f : X ⟶ Y) : ofHom (Hom.hom f) = f := rfl

@[simp]
/-
**PartOrd.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `PartOrd`。
形式化陈述：ofHom_id {X : Type u} [PartialOrder X] : ofHom OrderHom.id = 𝟙 (of X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {X : Type u} [PartialOrder X] : ofHom OrderHom.id = 𝟙 (of X) := rfl

@[simp]
/-
**PartOrd.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `PartOrd`。
形式化陈述：ofHom_comp {X Y Z : Type u} [PartialOrder X] [PartialOrder Y] [PartialOrde
r Z] (f : X ->o Y) (g : Y ->o Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g
参数：f : X ->o Y；g : Y ->o Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {X Y Z : Type u} [PartialOrder X] [PartialOrder Y] [PartialOrder Z]
    (f : X →o Y) (g : Y →o Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl
/-
**PartOrd.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `PartOrd`。
形式化陈述：ofHom_apply {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ->o Y)
 (x : X) : (ofHom f) x = f x
参数：f : X ->o Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X →o Y) (x : X) :
    (ofHom f) x = f x := rfl
/-
**PartOrd.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `PartOrd`。
形式化陈述：inv_hom_apply {X Y : PartOrd} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x
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
lemma inv_hom_apply {X Y : PartOrd} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp
/-
**PartOrd.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `PartOrd`。
形式化陈述：hom_inv_apply {X Y : PartOrd} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s
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
lemma hom_inv_apply {X Y : PartOrd} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp
/-
**PartOrd.hasForgetToPreord** 是 Mathlib 中的一个实例，位于命名空间 `PartOrd`。
形式化陈述：hasForgetToPreord : HasForget₂ PartOrd Preord where forget₂.obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToPreord : HasForget₂ PartOrd Preord where
  forget₂.obj X := .of X
  forget₂.map f := Preord.ofHom f.hom

/-- Constructs an equivalence between partial orders from an order isomorphism between them. -/
@[simps]
/-
**PartOrd.Iso.mk** 是 Mathlib 中的一个定义，位于命名空间 `PartOrd.Iso`。
形式化陈述：{α β : PartOrd} → ↑α ≃o ↑β → (α ≅ β)
参数：α ≅ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs an equivalence between partial orders from an order isomorphism betwe
en them.
-/
def Iso.mk {α β : PartOrd.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
/-
**PartOrd.dual** 是 Mathlib 中的一个定义，位于命名空间 `PartOrd`。
形式化陈述：dual : PartOrd ⥤ PartOrd where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrderDual` as a functor.
-/
def dual : PartOrd ⥤ PartOrd where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `PartOrd` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/-
**PartOrd.dualEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PartOrd`。
形式化陈述：dualEquiv : PartOrd ≌ PartOrd where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `PartOrd` and itself induced by `OrderDual` both ways.
-/
def dualEquiv : PartOrd ≌ PartOrd where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

/-- The ulift functor `PartOrd.{u} ⥤ PartOrd.{max u v}`. -/
@[simps]
/-
**PartOrd.uliftFunctor** 是 Mathlib 中的一个定义，位于命名空间 `PartOrd`。
形式化陈述：uliftFunctor : PartOrd.{u} ⥤ PartOrd.{max u v} where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ulift functor `PartOrd.{u} ⥤ PartOrd.{max u v}`.
-/
def uliftFunctor : PartOrd.{u} ⥤ PartOrd.{max u v} where
  obj X := .of (ULift.{v} X)
  map f := PartOrd.ofHom ⟨fun x ↦ ULift.up (f (ULift.down x)),
    fun x y hxy ↦ f.hom.monotone hxy⟩

end PartOrd

/-
**partOrd_dual_comp_forget_to_preord** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：partOrd_dual_comp_forget_to_preord : PartOrd.dual ⋙ forget₂ PartOrd Preord
 = forget₂ PartOrd Preord ⋙ Preord.dual
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem partOrd_dual_comp_forget_to_preord :
    PartOrd.dual ⋙ forget₂ PartOrd Preord =
      forget₂ PartOrd Preord ⋙ Preord.dual :=
  rfl

/-- `Antisymmetrization` as a functor. It is the free functor. -/
/-
**preordToPartOrd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：preordToPartOrd : Preord.{u} ⥤ PartOrd where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Antisymmetrization` as a functor. It is the free functor.
-/
def preordToPartOrd : Preord.{u} ⥤ PartOrd where
  obj X := .of (Antisymmetrization X (· ≤ ·))
  map f := PartOrd.ofHom f.hom.antisymmetrization
  map_id X := by
    ext x
    induction x using Quotient.inductionOn'
    exact Quotient.map'_mk'' _ (fun a b ↦ id) _
  map_comp f g := by
    ext x
    induction x using Quotient.inductionOn'
    exact OrderHom.antisymmetrization_apply_mk ..

/-- `preordToPartOrd` is left adjoint to the forgetful functor, meaning it is the free
functor from `Preord` to `PartOrd`. -/
/-
**preordToPartOrdForgetAdjunction** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：preordToPartOrdForgetAdjunction : preordToPartOrd.{u} ⊣ forget₂ PartOrd Pr
eord
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`preordToPartOrd` is left adjoint to the forgetful functor, meaning it is the fr
ee
functor from `Preord` to `PartOrd`.
-/
def preordToPartOrdForgetAdjunction :
    preordToPartOrd.{u} ⊣ forget₂ PartOrd Preord :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ :=
        { toFun f := Preord.ofHom
            ⟨f ∘ toAntisymmetrization (· ≤ ·), f.hom.mono.comp toAntisymmetrization_mono⟩
          invFun f := PartOrd.ofHom
            ⟨fun a => Quotient.liftOn' a f (fun _ _ h => (AntisymmRel.image h f.hom.mono).eq),
              fun a b => Quotient.inductionOn₂' a b fun _ _ h => f.hom.mono h⟩
          left_inv _ := PartOrd.ext fun x => Quotient.inductionOn' x fun _ => rfl }
      homEquiv_naturality_left_symm _ _ :=
        PartOrd.ext fun x => Quotient.inductionOn' x fun _ => rfl }

-- The `simpNF` linter would complain as `Functor.comp_obj`, `Preord.dual_obj` both apply to LHS
-- of `preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd_hom_app_coe`
/-- `PreordToPartOrd` and `OrderDual` commute. -/
@[simps! -isSimp hom_app_hom_coe inv_app_hom_coe]
/-
**preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd** 是 Mathlib 中的一个定义，位于命名空
间 ``。
形式化陈述：preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd : preordToPartOrd.{u
} ⋙ PartOrd.dual ≅ Preord.dual ⋙ preordToPartOrd
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PreordToPartOrd` and `OrderDual` commute.
-/
def preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd :
    preordToPartOrd.{u} ⋙ PartOrd.dual ≅ Preord.dual ⋙ preordToPartOrd :=
  NatIso.ofComponents (fun _ => PartOrd.Iso.mk <| OrderIso.dualAntisymmetrization _)
    (fun _ => PartOrd.ext fun x => Quotient.inductionOn' x fun _ => rfl)

-- `simp`-normal form for `preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd_inv_app_hom_coe`
@[simp]
/-
**preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd_inv_app_hom_coe'** 是 Mat
hlib 中的一个引理，位于命名空间 ``。
形式化陈述：preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd_inv_app_hom_coe' (X)
 (a : preordToPartOrd.obj (Preord.dual.obj X)) : (PartOrd.Hom.hom (X
参数：X；a : preordToPartOrd.obj (Preord.dual.obj X)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd_inv_app_hom_coe' (X)
    (a : preordToPartOrd.obj (Preord.dual.obj X)) :
    (PartOrd.Hom.hom
        (X := preordToPartOrd.obj (Preord.dual.obj X))
        (Y := PartOrd.dual.obj (preordToPartOrd.obj X))
        (preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd.inv.app X)) a =
      (OrderIso.dualAntisymmetrization ↑X).symm a :=
  rfl
