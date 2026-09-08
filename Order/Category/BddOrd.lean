/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.CategoryTheory.Category.Bipointed
public import Mathlib.Order.Category.PartOrd
public import Mathlib.Order.Hom.Bounded

/-!
# The category of bounded orders

This defines `BddOrd`, the category of bounded orders.
-/

@[expose] public section


universe u v

open CategoryTheory

/-- The category of bounded orders with monotone functions. -/
/-
**BddOrd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u_1 + 1)
参数：u_1 + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of bounded orders with monotone functions.
-/
structure BddOrd extends PartOrd where
  [isBoundedOrder : BoundedOrder toPartOrd]

/-- The underlying object in the category of partial orders. -/
add_decl_doc BddOrd.toPartOrd

attribute [instance] BddOrd.isBoundedOrder

initialize_simps_projections BddOrd (carrier → coe, -str)

namespace BddOrd

/-
**BddOrd.** 是 Mathlib 中的一个实例，位于命名空间 `BddOrd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort BddOrd Type* :=
  InducedCategory.hasCoeToSort toPartOrd

/-- Construct a bundled `BddOrd` from the underlying type and typeclass. -/
/-
**BddOrd.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `BddOrd`。
形式化陈述：of (X : Type*) [PartialOrder X] [BoundedOrder X] : BddOrd where carrier
参数：X : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `BddOrd` from the underlying type and typeclass.
-/
abbrev of (X : Type*) [PartialOrder X] [BoundedOrder X] : BddOrd where
  carrier := X

/-- The type of morphisms in `BddOrd R`. -/
@[ext]
/-
**BddOrd.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `BddOrd`。
形式化陈述：BddOrd → BddOrd → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `BddOrd R`.
-/
structure Hom (X Y : BddOrd.{u}) where
  private mk ::
  /-- The underlying `BoundedOrderHom`. -/
  hom' : BoundedOrderHom X Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**BddOrd.** 是 Mathlib 中的一个实例，位于命名空间 `BddOrd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category BddOrd.{u} where
  Hom X Y := Hom X Y
  id _ := ⟨BoundedOrderHom.id _⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**BddOrd.** 是 Mathlib 中的一个实例，位于命名空间 `BddOrd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory BddOrd (BoundedOrderHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `BddOrd` back into a `BoundedOrderHom`. -/
/-
**BddOrd.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `BddOrd.Hom`。
形式化陈述：{X Y : BddOrd} → X.Hom Y → BoundedOrderHom ↑X.toPartOrd ↑Y.toPartOrd
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `BddOrd` back into a `BoundedOrderHom`.
-/
abbrev Hom.hom {X Y : BddOrd.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := BddOrd) f

/-- Typecheck a `BoundedOrderHom` as a morphism in `BddOrd`. -/
/-
**BddOrd.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `BddOrd`。
形式化陈述：ofHom {X Y : Type u} [PartialOrder X] [BoundedOrder X] [PartialOrder Y] [B
oundedOrder Y] (f : BoundedOrderHom X Y) : of X ⟶ of Y
参数：f : BoundedOrderHom X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `BoundedOrderHom` as a morphism in `BddOrd`.
-/
abbrev ofHom {X Y : Type u} [PartialOrder X] [BoundedOrder X] [PartialOrder Y] [BoundedOrder Y]
    (f : BoundedOrderHom X Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := BddOrd) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**BddOrd.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `BddOrd.Hom.Simps`。
形式化陈述：(X Y : BddOrd) → X.Hom Y → BoundedOrderHom ↑X.toPartOrd ↑Y.toPartOrd
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (X Y : BddOrd.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/-
**BddOrd.coe_id** 是 Mathlib 中的一个引理，位于命名空间 `BddOrd`。
形式化陈述：coe_id {X : BddOrd} : (𝟙 X : X -> X) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma coe_id {X : BddOrd} : (𝟙 X : X → X) = id := rfl

@[simp]
/-
**BddOrd.coe_comp** 是 Mathlib 中的一个引理，位于命名空间 `BddOrd`。
形式化陈述：coe_comp {X Y Z : BddOrd} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g ∘
 f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comp {X Y Z : BddOrd} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[simp]
/-
**BddOrd.forget_map** 是 Mathlib 中的一个引理，位于命名空间 `BddOrd`。
形式化陈述：forget_map {X Y : BddOrd} (f : X ⟶ Y) : (forget BddOrd).map f = (f : _ -> 
_)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_map {X Y : BddOrd} (f : X ⟶ Y) :
    (forget BddOrd).map f = (f : _ → _) := rfl

@[ext]
/-
**BddOrd.ext** 是 Mathlib 中的一个引理，位于命名空间 `BddOrd`。
形式化陈述：ext {X Y : BddOrd} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g
参数：w : forall x : X, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
-/
lemma ext {X Y : BddOrd} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
/-
**BddOrd.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `BddOrd`。
形式化陈述：coe_of (X : Type u) [PartialOrder X] [BoundedOrder X] : (BddOrd.of X : Typ
e u) = X
参数：X : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (X : Type u) [PartialOrder X] [BoundedOrder X] : (BddOrd.of X : Type u) = X := rfl

@[simp]
/-
**BddOrd.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `BddOrd`。
形式化陈述：hom_id {X : BddOrd} : (𝟙 X : X ⟶ X).hom = BoundedOrderHom.id _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_id {X : BddOrd} : (𝟙 X : X ⟶ X).hom = BoundedOrderHom.id _ := rfl

/- Provided for rewriting. -/
/-
**BddOrd.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `BddOrd`。
形式化陈述：id_apply (X : BddOrd) (x : X) : (𝟙 X : X ⟶ X) x = x
参数：X : BddOrd；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (X : BddOrd) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/-
**BddOrd.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `BddOrd`。
形式化陈述：hom_comp {X Y Z : BddOrd} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = g.hom.co
mp f.hom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {X Y Z : BddOrd} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
/-
**BddOrd.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `BddOrd`。
形式化陈述：comp_apply {X Y Z : BddOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = 
g (f x)
参数：f : X ⟶ Y；g : Y ⟶ Z；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {X Y Z : BddOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/-
**BddOrd.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `BddOrd`。
形式化陈述：hom_ext {X Y : BddOrd} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BddOrd.Hom.ext`：∀ {X Y : BddOrd} {x y : X.Hom Y}, x.hom' = y.hom' → x = 
y
-/
lemma hom_ext {X Y : BddOrd} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/-
**BddOrd.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `BddOrd`。
形式化陈述：hom_ofHom {X Y : Type u} [PartialOrder X] [BoundedOrder X] [PartialOrder Y
] [BoundedOrder Y] (f : BoundedOrderHom X Y) : (ofHom f).hom = f
参数：f : BoundedOrderHom X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {X Y : Type u} [PartialOrder X] [BoundedOrder X] [PartialOrder Y] [BoundedOrder Y]
    (f : BoundedOrderHom X Y) :
    (ofHom f).hom = f := rfl

@[simp]
/-
**BddOrd.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `BddOrd`。
形式化陈述：ofHom_hom {X Y : BddOrd} (f : X ⟶ Y) : ofHom f.hom = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {X Y : BddOrd} (f : X ⟶ Y) :
    ofHom f.hom = f := rfl

@[simp]
/-
**BddOrd.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `BddOrd`。
形式化陈述：ofHom_id {X : Type u} [PartialOrder X] [BoundedOrder X] : ofHom (BoundedOr
derHom.id _) = 𝟙 (of X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {X : Type u} [PartialOrder X] [BoundedOrder X] :
    ofHom (BoundedOrderHom.id _) = 𝟙 (of X) := rfl

@[simp]
/-
**BddOrd.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `BddOrd`。
形式化陈述：ofHom_comp {X Y Z : Type u} [PartialOrder X] [BoundedOrder X] [PartialOrde
r Y] [BoundedOrder Y] [PartialOrder Z] [BoundedOrder Z] (f : BoundedOrderHom X Y
) (g : BoundedOrderHom Y Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g
参数：f : BoundedOrderHom X Y；g : BoundedOrderHom Y Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {X Y Z : Type u} [PartialOrder X] [BoundedOrder X] [PartialOrder Y]
    [BoundedOrder Y] [PartialOrder Z] [BoundedOrder Z]
    (f : BoundedOrderHom X Y) (g : BoundedOrderHom Y Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl
/-
**BddOrd.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `BddOrd`。
形式化陈述：ofHom_apply {X Y : Type u} [PartialOrder X] [BoundedOrder X] [PartialOrder
 Y] [BoundedOrder Y] (f : BoundedOrderHom X Y) (x : X) : ofHom f x = f x
参数：f : BoundedOrderHom X Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {X Y : Type u} [PartialOrder X] [BoundedOrder X] [PartialOrder Y] [BoundedOrder Y]
    (f : BoundedOrderHom X Y) (x : X) :
    ofHom f x = f x := rfl
/-
**BddOrd.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `BddOrd`。
形式化陈述：inv_hom_apply {X Y : BddOrd} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x
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
lemma inv_hom_apply {X Y : BddOrd} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp
/-
**BddOrd.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `BddOrd`。
形式化陈述：hom_inv_apply {X Y : BddOrd} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s
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
lemma hom_inv_apply {X Y : BddOrd} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp
/-
**BddOrd.** 是 Mathlib 中的一个实例，位于命名空间 `BddOrd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited BddOrd :=
  ⟨of PUnit⟩
/-
**BddOrd.hasForgetToPartOrd** 是 Mathlib 中的一个实例，位于命名空间 `BddOrd`。
形式化陈述：hasForgetToPartOrd : HasForget₂ BddOrd PartOrd where forget₂.obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToPartOrd : HasForget₂ BddOrd PartOrd where
  forget₂.obj X := X.toPartOrd
  forget₂.map f := PartOrd.ofHom f.hom.toOrderHom
/-
**BddOrd.hasForgetToBipointed** 是 Mathlib 中的一个实例，位于命名空间 `BddOrd`。
形式化陈述：hasForgetToBipointed : HasForget₂ BddOrd Bipointed where forget₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToBipointed : HasForget₂ BddOrd Bipointed where
  forget₂ :=
    { obj := fun X => ⟨X, ⊥, ⊤⟩
      map := fun f => ⟨f, f.hom.map_bot', f.hom.map_top'⟩ }
  forget_comp := rfl

/-- `OrderDual` as a functor. -/
@[simps map]
/-
**BddOrd.dual** 是 Mathlib 中的一个定义，位于命名空间 `BddOrd`。
形式化陈述：dual : BddOrd ⥤ BddOrd where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrderDual` as a functor.
-/
def dual : BddOrd ⥤ BddOrd where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- Constructs an equivalence between bounded orders from an order isomorphism between them. -/
@[simps]
/-
**BddOrd.Iso.mk** 是 Mathlib 中的一个定义，位于命名空间 `BddOrd.Iso`。
形式化陈述：{α β : BddOrd} → ↑α.toPartOrd ≃o ↑β.toPartOrd → (α ≅ β)
参数：α ≅ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs an equivalence between bounded orders from an order isomorphism betwe
en them.
-/
def Iso.mk {α β : BddOrd.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

/-- The equivalence between `BddOrd` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/-
**BddOrd.dualEquiv** 是 Mathlib 中的一个定义，位于命名空间 `BddOrd`。
形式化陈述：dualEquiv : BddOrd ≌ BddOrd where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `BddOrd` and itself induced by `OrderDual` both ways.
-/
def dualEquiv : BddOrd ≌ BddOrd where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

end BddOrd

/-
**bddOrd_dual_comp_forget_to_partOrd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bddOrd_dual_comp_forget_to_partOrd : BddOrd.dual ⋙ forget₂ BddOrd PartOrd 
= forget₂ BddOrd PartOrd ⋙ PartOrd.dual
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bddOrd_dual_comp_forget_to_partOrd :
    BddOrd.dual ⋙ forget₂ BddOrd PartOrd =
    forget₂ BddOrd PartOrd ⋙ PartOrd.dual :=
  rfl
/-
**bddOrd_dual_comp_forget_to_bipointed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bddOrd_dual_comp_forget_to_bipointed : BddOrd.dual ⋙ forget₂ BddOrd Bipoin
ted = forget₂ BddOrd Bipointed ⋙ Bipointed.swap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bddOrd_dual_comp_forget_to_bipointed :
    BddOrd.dual ⋙ forget₂ BddOrd Bipointed =
    forget₂ BddOrd Bipointed ⋙ Bipointed.swap :=
  rfl
