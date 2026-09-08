/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.Order.Category.PartOrd

/-!
# The category of finite partial orders

This defines `FinPartOrd`, the category of finite partial orders.

Note: `FinPartOrd` is *not* a subcategory of `BddOrd` because finite orders are not necessarily
bounded.

## TODO

`FinPartOrd` is equivalent to a small category.
-/

@[expose] public section


universe u v

open CategoryTheory


/-- The category of finite partial orders with monotone functions. -/
/-
**FinPartOrd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u_1 + 1)
参数：u_1 + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of finite partial orders with monotone functions.
-/
structure FinPartOrd extends PartOrd where
  [isFintype : Fintype toPartOrd]

namespace FinPartOrd

/-
**FinPartOrd.** 是 Mathlib 中的一个实例，位于命名空间 `FinPartOrd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort FinPartOrd Type* :=
  ⟨fun X => X.toPartOrd⟩
/-
**FinPartOrd.** 是 Mathlib 中的一个实例，位于命名空间 `FinPartOrd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : FinPartOrd) : PartialOrder X :=
  X.toPartOrd.str

attribute [instance] FinPartOrd.isFintype

/-- Construct a bundled `FinPartOrd` from `PartialOrder` + `Fintype`. -/
/-
**FinPartOrd.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `FinPartOrd`。
形式化陈述：of (α : Type*) [PartialOrder α] [Fintype α] : FinPartOrd where carrier
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `FinPartOrd` from `PartialOrder` + `Fintype`.
-/
abbrev of (α : Type*) [PartialOrder α] [Fintype α] : FinPartOrd where
  carrier := α
/-
**FinPartOrd.** 是 Mathlib 中的一个实例，位于命名空间 `FinPartOrd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited FinPartOrd :=
  ⟨of PUnit⟩
/-
**FinPartOrd.largeCategory** 是 Mathlib 中的一个实例，位于命名空间 `FinPartOrd`。
形式化陈述：largeCategory : LargeCategory FinPartOrd
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance largeCategory : LargeCategory FinPartOrd :=
  inferInstanceAs <| Category (InducedCategory _ toPartOrd)
/-
**FinPartOrd.concreteCategory** 是 Mathlib 中的一个实例，位于命名空间 `FinPartOrd`。
形式化陈述：concreteCategory : ConcreteCategory FinPartOrd (· ->o ·)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance concreteCategory : ConcreteCategory FinPartOrd (· →o ·) :=
  inferInstanceAs <| ConcreteCategory (InducedCategory _ toPartOrd) _
/-
**FinPartOrd.hasForgetToPartOrd** 是 Mathlib 中的一个实例，位于命名空间 `FinPartOrd`。
形式化陈述：hasForgetToPartOrd : HasForget₂ FinPartOrd PartOrd
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToPartOrd : HasForget₂ FinPartOrd PartOrd :=
  inferInstanceAs <| HasForget₂ (InducedCategory _ toPartOrd) _
/-
**FinPartOrd.hasForgetToFintype** 是 Mathlib 中的一个实例，位于命名空间 `FinPartOrd`。
形式化陈述：hasForgetToFintype : HasForget₂ FinPartOrd FintypeCat where forget₂.obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToFintype : HasForget₂ FinPartOrd FintypeCat where
  forget₂.obj X := .of X
  forget₂.map f := FintypeCat.homMk f.hom

/-- Typecheck a `OrderHom` as a morphism in `FinPartOrd`. -/
/-
**FinPartOrd.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `FinPartOrd`。
形式化陈述：ofHom {X Y : Type u} [PartialOrder X] [Fintype X] [PartialOrder Y] [Fintyp
e Y] (f : X ->o Y) : of X ⟶ of Y
参数：f : X ->o Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `OrderHom` as a morphism in `FinPartOrd`.
-/
abbrev ofHom {X Y : Type u} [PartialOrder X] [Fintype X] [PartialOrder Y] [Fintype Y] (f : X →o Y) :
    of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := FinPartOrd) f

@[simp]
/-
**FinPartOrd.hom_hom_id** 是 Mathlib 中的一个引理，位于命名空间 `FinPartOrd`。
形式化陈述：hom_hom_id {X : FinPartOrd} : (𝟙 X : X ⟶ X).hom.hom = OrderHom.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_hom_id {X : FinPartOrd} : (𝟙 X : X ⟶ X).hom.hom = OrderHom.id := rfl

/- Provided for rewriting. -/
/-
**FinPartOrd.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `FinPartOrd`。
形式化陈述：id_apply (X : FinPartOrd) (x : X) : (𝟙 X : X ⟶ X) x = x
参数：X : FinPartOrd；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (X : FinPartOrd) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/-
**FinPartOrd.hom_hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `FinPartOrd`。
形式化陈述：hom_hom_comp {X Y Z : FinPartOrd} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom.ho
m = g.hom.hom.comp f.hom.hom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_hom_comp {X Y Z : FinPartOrd} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom.hom = g.hom.hom.comp f.hom.hom := rfl

/- Provided for rewriting. -/
/-
**FinPartOrd.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `FinPartOrd`。
形式化陈述：comp_apply {X Y Z : FinPartOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) 
x = g (f x)
参数：f : X ⟶ Y；g : Y ⟶ Z；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {X Y Z : FinPartOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/-
**FinPartOrd.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `FinPartOrd`。
形式化陈述：hom_ext {X Y : FinPartOrd} {f g : X ⟶ Y} (hf : f.hom.hom = g.hom.hom) : f 
= g
参数：hf : f.hom.hom = g.hom.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.InducedCategory.hom_ext`：hom_ext {X Y : InducedCategory D
 F} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
-/
lemma hom_ext {X Y : FinPartOrd} {f g : X ⟶ Y} (hf : f.hom.hom = g.hom.hom) : f = g :=
  InducedCategory.hom_ext (ConcreteCategory.ext hf)

@[simp]
/-
**FinPartOrd.hom_hom_ofHom** 是 Mathlib 中的一个引理，位于命名空间 `FinPartOrd`。
形式化陈述：hom_hom_ofHom {X Y : Type u} [PartialOrder X] [Fintype X] [PartialOrder Y]
 [Fintype Y] (f : X ->o Y) : (ofHom f).hom.hom = f
参数：f : X ->o Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_hom_ofHom {X Y : Type u} [PartialOrder X] [Fintype X] [PartialOrder Y] [Fintype Y]
    (f : X →o Y) :
  (ofHom f).hom.hom = f := rfl

@[simp]
/-
**FinPartOrd.ofHom_hom_hom** 是 Mathlib 中的一个引理，位于命名空间 `FinPartOrd`。
形式化陈述：ofHom_hom_hom {X Y : FinPartOrd} (f : X ⟶ Y) : ofHom f.hom.hom = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_hom_hom {X Y : FinPartOrd} (f : X ⟶ Y) :
    ofHom f.hom.hom = f := rfl

/-- Constructs an isomorphism of finite partial orders from an order isomorphism between them. -/
@[simps]
/-
**FinPartOrd.Iso.mk** 是 Mathlib 中的一个定义，位于命名空间 `FinPartOrd.Iso`。
形式化陈述：{α β : FinPartOrd} → ↑α.toPartOrd ≃o ↑β.toPartOrd → (α ≅ β)
参数：α ≅ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs an isomorphism of finite partial orders from an order isomorphism bet
ween them.
-/
def Iso.mk {α β : FinPartOrd.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
/-
**FinPartOrd.dual** 是 Mathlib 中的一个定义，位于命名空间 `FinPartOrd`。
形式化陈述：dual : FinPartOrd ⥤ FinPartOrd where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrderDual` as a functor.
-/
def dual : FinPartOrd ⥤ FinPartOrd where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.hom.dual

/-- The equivalence between `FinPartOrd` and itself induced by `OrderDual` both ways. -/
@[simps]
/-
**FinPartOrd.dualEquiv** 是 Mathlib 中的一个定义，位于命名空间 `FinPartOrd`。
形式化陈述：dualEquiv : FinPartOrd ≌ FinPartOrd where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `FinPartOrd` and itself induced by `OrderDual` both ways
.
-/
def dualEquiv : FinPartOrd ≌ FinPartOrd where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

end FinPartOrd

/-
**FinPartOrd_dual_comp_forget_to_partOrd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FinPartOrd_dual_comp_forget_to_partOrd : FinPartOrd.dual ⋙ forget₂ FinPart
Ord PartOrd = forget₂ FinPartOrd PartOrd ⋙ PartOrd.dual
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem FinPartOrd_dual_comp_forget_to_partOrd :
    FinPartOrd.dual ⋙ forget₂ FinPartOrd PartOrd =
      forget₂ FinPartOrd PartOrd ⋙ PartOrd.dual := rfl
