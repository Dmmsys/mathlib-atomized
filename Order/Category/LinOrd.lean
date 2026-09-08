/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Order.Category.Lat

/-!
# Category of linear orders

This defines `LinOrd`, the category of linear orders with monotone maps.
-/

@[expose] public section


open CategoryTheory

universe u

namespace LinOrd

/-- The type of morphisms in `LinOrd R`. -/
@[ext]
/-
**LinOrd.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `LinOrd`。
形式化陈述：LinOrd → LinOrd → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `LinOrd R`.
-/
structure Hom (X Y : LinOrd.{u}) where
  private mk ::
  /-- The underlying `OrderHom`. -/
  hom' : X →o Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**LinOrd.** 是 Mathlib 中的一个实例，位于命名空间 `LinOrd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category LinOrd.{u} where
  Hom X Y := Hom X Y
  id _ := ⟨OrderHom.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**LinOrd.** 是 Mathlib 中的一个实例，位于命名空间 `LinOrd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory LinOrd (· →o ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `LinOrd` back into a `OrderHom`. -/
/-
**LinOrd.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `LinOrd.Hom`。
形式化陈述：{X Y : LinOrd} → X.Hom Y → ↑X →o ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `LinOrd` back into a `OrderHom`.
-/
abbrev Hom.hom {X Y : LinOrd.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := LinOrd) f

/-- Typecheck a `OrderHom` as a morphism in `LinOrd`. -/
/-
**LinOrd.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `LinOrd`。
形式化陈述：ofHom {X Y : Type u} [LinearOrder X] [LinearOrder Y] (f : X ->o Y) : of X 
⟶ of Y
参数：f : X ->o Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `OrderHom` as a morphism in `LinOrd`.
-/
abbrev ofHom {X Y : Type u} [LinearOrder X] [LinearOrder Y] (f : X →o Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := LinOrd) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**LinOrd.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `LinOrd.Hom.Simps`。
形式化陈述：(X Y : LinOrd) → X.Hom Y → ↑X →o ↑Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (X Y : LinOrd.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

/-
**LinOrd.coe_id** 是 Mathlib 中的一个引理，位于命名空间 `LinOrd`。
形式化陈述：coe_id {X : LinOrd} : (𝟙 X : X -> X) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep 
them for `dsimp`.
-/
lemma coe_id {X : LinOrd} : (𝟙 X : X → X) = id := rfl
/-
**LinOrd.coe_comp** 是 Mathlib 中的一个引理，位于命名空间 `LinOrd`。
形式化陈述：coe_comp {X Y Z : LinOrd} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g ∘
 f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_comp {X Y Z : LinOrd} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[simp]
/-
**LinOrd.forget_map** 是 Mathlib 中的一个引理，位于命名空间 `LinOrd`。
形式化陈述：forget_map {X Y : LinOrd} (f : X ⟶ Y) : (forget LinOrd).map f = (f : _ -> 
_)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_map {X Y : LinOrd} (f : X ⟶ Y) :
    (forget LinOrd).map f = (f : _ → _) := rfl

@[ext]
/-
**LinOrd.ext** 是 Mathlib 中的一个引理，位于命名空间 `LinOrd`。
形式化陈述：ext {X Y : LinOrd} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g
参数：w : forall x : X, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
-/
lemma ext {X Y : LinOrd} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
/-
**LinOrd.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `LinOrd`。
形式化陈述：coe_of (X : Type u) [LinearOrder X] : (LinOrd.of X : Type u) = X
参数：X : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (X : Type u) [LinearOrder X] : (LinOrd.of X : Type u) = X := rfl

@[simp]
/-
**LinOrd.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `LinOrd`。
形式化陈述：hom_id {X : LinOrd} : (𝟙 X : X ⟶ X).hom = OrderHom.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_id {X : LinOrd} : (𝟙 X : X ⟶ X).hom = OrderHom.id := rfl

/- Provided for rewriting. -/
/-
**LinOrd.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `LinOrd`。
形式化陈述：id_apply (X : LinOrd) (x : X) : (𝟙 X : X ⟶ X) x = x
参数：X : LinOrd；x : X。
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
lemma id_apply (X : LinOrd) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/-
**LinOrd.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `LinOrd`。
形式化陈述：hom_comp {X Y Z : LinOrd} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = g.hom.co
mp f.hom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {X Y Z : LinOrd} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
/-
**LinOrd.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `LinOrd`。
形式化陈述：comp_apply {X Y Z : LinOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = 
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
lemma comp_apply {X Y Z : LinOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/-
**LinOrd.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `LinOrd`。
形式化陈述：hom_ext {X Y : LinOrd} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinOrd.Hom.ext`：∀ {X Y : LinOrd} {x y : X.Hom Y}, x.hom' = y.hom' → x = 
y
-/
lemma hom_ext {X Y : LinOrd} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/-
**LinOrd.hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `LinOrd`。
形式化陈述：hom_ofHom {X Y : Type u} [LinearOrder X] [LinearOrder Y] (f : X ->o Y) : (
ofHom f).hom = f
参数：f : X ->o Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ofHom {X Y : Type u} [LinearOrder X] [LinearOrder Y] (f : X →o Y) : (ofHom f).hom = f :=
  rfl

@[simp]
/-
**LinOrd.ofHom_hom** 是 Mathlib 中的一个引理，位于命名空间 `LinOrd`。
形式化陈述：ofHom_hom {X Y : LinOrd} (f : X ⟶ Y) : ofHom (Hom.hom f) = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom {X Y : LinOrd} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/-
**LinOrd.ofHom_id** 是 Mathlib 中的一个引理，位于命名空间 `LinOrd`。
形式化陈述：ofHom_id {X : Type u} [LinearOrder X] : ofHom OrderHom.id = 𝟙 (of X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_id {X : Type u} [LinearOrder X] : ofHom OrderHom.id = 𝟙 (of X) := rfl

@[simp]
/-
**LinOrd.ofHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `LinOrd`。
形式化陈述：ofHom_comp {X Y Z : Type u} [LinearOrder X] [LinearOrder Y] [LinearOrder Z
] (f : X ->o Y) (g : Y ->o Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g
参数：f : X ->o Y；g : Y ->o Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_comp {X Y Z : Type u} [LinearOrder X] [LinearOrder Y] [LinearOrder Z]
    (f : X →o Y) (g : Y →o Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl
/-
**LinOrd.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `LinOrd`。
形式化陈述：ofHom_apply {X Y : Type u} [LinearOrder X] [LinearOrder Y] (f : X ->o Y) (
x : X) : (ofHom f) x = f x
参数：f : X ->o Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {X Y : Type u} [LinearOrder X] [LinearOrder Y] (f : X →o Y) (x : X) :
    (ofHom f) x = f x := rfl
/-
**LinOrd.inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `LinOrd`。
形式化陈述：inv_hom_apply {X Y : LinOrd} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x
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
lemma inv_hom_apply {X Y : LinOrd} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp
/-
**LinOrd.hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `LinOrd`。
形式化陈述：hom_inv_apply {X Y : LinOrd} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s
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
lemma hom_inv_apply {X Y : LinOrd} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp
/-
**LinOrd.** 是 Mathlib 中的一个实例，位于命名空间 `LinOrd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited LinOrd :=
  ⟨of PUnit⟩
/-
**LinOrd.hasForgetToLat** 是 Mathlib 中的一个实例，位于命名空间 `LinOrd`。
形式化陈述：hasForgetToLat : HasForget₂ LinOrd Lat where forget₂.obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToLat : HasForget₂ LinOrd Lat where
  forget₂.obj X := .of X
  forget₂.map f := Lat.ofHom (OrderHomClass.toLatticeHom _ _ f.hom)

/-- Constructs an equivalence between linear orders from an order isomorphism between them. -/
@[simps]
/-
**LinOrd.Iso.mk** 是 Mathlib 中的一个定义，位于命名空间 `LinOrd.Iso`。
形式化陈述：{α β : LinOrd} → ↑α ≃o ↑β → (α ≅ β)
参数：α ≅ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs an equivalence between linear orders from an order isomorphism betwee
n them.
-/
def Iso.mk {α β : LinOrd.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
/-
**LinOrd.dual** 是 Mathlib 中的一个定义，位于命名空间 `LinOrd`。
形式化陈述：dual : LinOrd ⥤ LinOrd where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrderDual` as a functor.
-/
def dual : LinOrd ⥤ LinOrd where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `LinOrd` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/-
**LinOrd.dualEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LinOrd`。
形式化陈述：dualEquiv : LinOrd ≌ LinOrd where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `LinOrd` and itself induced by `OrderDual` both ways.
-/
def dualEquiv : LinOrd ≌ LinOrd where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

end LinOrd

/-
**linOrd_dual_comp_forget_to_Lat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linOrd_dual_comp_forget_to_Lat : LinOrd.dual ⋙ forget₂ LinOrd Lat = forget
₂ LinOrd Lat ⋙ Lat.dual
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linOrd_dual_comp_forget_to_Lat :
    LinOrd.dual ⋙ forget₂ LinOrd Lat = forget₂ LinOrd Lat ⋙ Lat.dual :=
  rfl
