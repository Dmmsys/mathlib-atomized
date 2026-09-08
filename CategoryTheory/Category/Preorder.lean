/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Kim Morrison, Johannes Hölzl, Reid Barton
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.Order.Hom.Basic
public import Mathlib.Data.ULift

/-!

# Preorders as categories

We install a category instance on any preorder. This is not to be confused with the category _of_
preorders, defined in `Order.Category.Preorder`.

We show that monotone functions between preorders correspond to functors of the associated
categories.

## Main definitions

* `homOfLE` and `leOfHom` provide translations between inequalities in the preorder, and
  morphisms in the associated category.
* `Monotone.functor` is the functor associated to a monotone function.

-/

@[expose] public section


universe u v

namespace Preorder

open CategoryTheory

-- see Note [lower instance priority]
/--
The category structure coming from a preorder. There is a morphism `X ⟶ Y` if and only if `X ≤ Y`.

Because we don't allow morphisms to live in `Prop`,
we have to define `X ⟶ Y` as `ULift (PLift (X ≤ Y))`.
See `CategoryTheory.homOfLE` and `CategoryTheory.leOfHom`. -/
@[stacks 00D3]
/-
**Preorder.** 是 Mathlib 中的一个实例，位于命名空间 `Preorder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category structure coming from a preorder. There is a morphism `X ⟶ Y` if an
d only if `X ≤ Y`.

Because we don't allow morphisms to live in `Prop`,
we have to define `X ⟶ Y` as `ULift (PLift (X ≤ Y))`.
See `CategoryTheory.homOfLE` and `CategoryTheory.leOfHom`.
-/
instance (priority := 100) smallCategory (α : Type u) [Preorder α] : SmallCategory α where
  Hom U V := ULift (PLift (U ≤ V))
  id X := ⟨⟨le_refl X⟩⟩
  comp f g := ⟨⟨le_trans f.down.down g.down.down⟩⟩
/-
**Preorder.subsingleton_hom** 是 Mathlib 中的一个实例，位于命名空间 `Preorder`。
形式化陈述：subsingleton_hom {α : Type u} [Preorder α] (U V : α) : Subsingleton (U ⟶ V
)
参数：U V : α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ULift.ext`：ext (x y : ULift α) (h : x.down = y.down) : x = y
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonPLift`：∀ {α : Sort u_1} [Subsingleton α], Subsingleton (
PLift α)
· 使用定理 `instSubsingleton`：∀ (p : Prop), Subsingleton p
-/
instance subsingleton_hom {α : Type u} [Preorder α] (U V : α) : Subsingleton (U ⟶ V) :=
  ⟨fun _ _ => ULift.ext _ _ (Subsingleton.elim _ _ )⟩

end Preorder

namespace CategoryTheory

open Opposite

variable {X : Type u} [Preorder X]

/-- Express an inequality as a morphism in the corresponding preorder category. -/
/-
**CategoryTheory.homOfLE** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：homOfLE {x y : X} (h : x <= y) : x ⟶ y
参数：h : x <= y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Express an inequality as a morphism in the corresponding preorder category.
-/
def homOfLE {x y : X} (h : x ≤ y) : x ⟶ y :=
  ULift.up (PLift.up h)

@[inherit_doc homOfLE]
/-
**CategoryTheory._root_.LE.le.hom** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev _root_.LE.le.hom := @homOfLE

@[simp]
/-
**CategoryTheory.homOfLE_refl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：homOfLE_refl {x : X} (h : x <= x) : h.hom = 𝟙 x
参数：h : x <= x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homOfLE_refl {x : X} (h : x ≤ x) : h.hom = 𝟙 x :=
  rfl

@[simp]
/-
**CategoryTheory.homOfLE_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：homOfLE_comp {x y z : X} (h : x <= y) (k : y <= z) : homOfLE h ≫ homOfLE k
 = homOfLE (h.trans k)
参数：h : x <= y；k : y <= z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homOfLE_comp {x y z : X} (h : x ≤ y) (k : y ≤ z) :
    homOfLE h ≫ homOfLE k = homOfLE (h.trans k) :=
  rfl

/-- Extract the underlying inequality from a morphism in a preorder category. -/
/-
**CategoryTheory.leOfHom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：leOfHom {x y : X} (h : x ⟶ y) : x <= y
参数：h : x ⟶ y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract the underlying inequality from a morphism in a preorder category.
-/
theorem leOfHom {x y : X} (h : x ⟶ y) : x ≤ y :=
  h.down.down

set_option linter.defProp false in
@[inherit_doc leOfHom]
/-
**CategoryTheory._root_.Quiver.Hom.le** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev _root_.Quiver.Hom.le := @leOfHom

@[simp]
/-
**CategoryTheory.homOfLE_leOfHom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：homOfLE_leOfHom {x y : X} (h : x ⟶ y) : h.le.hom = h
参数：h : x ⟶ y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homOfLE_leOfHom {x y : X} (h : x ⟶ y) : h.le.hom = h :=
  rfl
/-
**CategoryTheory.homOfLE_isIso_of_eq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：homOfLE_isIso_of_eq {x y : X} (h : x <= y) (heq : x = y) : IsIso (homOfLE 
h)
参数：h : x <= y；heq : x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma homOfLE_isIso_of_eq {x y : X} (h : x ≤ y) (heq : x = y) :
    IsIso (homOfLE h) :=
  ⟨homOfLE (le_of_eq heq.symm), by simp⟩
/-
**CategoryTheory.isIso_homOfLE** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：isIso_homOfLE {x y : X} (h : x = y) : IsIso (homOfLE (by rw [h]) : x ⟶ y)
参数：h : x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_homOfLE {x y : X} (h : x = y) :
    IsIso (homOfLE (by rw [h]) : x ⟶ y) := by
  subst h
  change IsIso (𝟙 _)
  infer_instance

@[simp, reassoc]
/-
**CategoryTheory.homOfLE_comp_eqToHom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`
。
形式化陈述：homOfLE_comp_eqToHom {a b c : X} (hab : a <= b) (hbc : b = c) : homOfLE ha
b ≫ eqToHom hbc = homOfLE (hab.trans (le_of_eq hbc))
参数：hab : a <= b；hbc : b = c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homOfLE_comp_eqToHom {a b c : X} (hab : a ≤ b) (hbc : b = c) :
    homOfLE hab ≫ eqToHom hbc = homOfLE (hab.trans (le_of_eq hbc)) :=
  rfl

@[simp, reassoc]
/-
**CategoryTheory.eqToHom_comp_homOfLE** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`
。
形式化陈述：eqToHom_comp_homOfLE {a b c : X} (hab : a = b) (hbc : b <= c) : eqToHom ha
b ≫ homOfLE hbc = homOfLE ((le_of_eq hab).trans hbc)
参数：hab : a = b；hbc : b <= c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eqToHom_comp_homOfLE {a b c : X} (hab : a = b) (hbc : b ≤ c) :
    eqToHom hab ≫ homOfLE hbc = homOfLE ((le_of_eq hab).trans hbc) :=
  rfl

@[simp, reassoc]
/-
**CategoryTheory.homOfLE_op_comp_eqToHom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：homOfLE_op_comp_eqToHom {a b c : X} (hab : b <= a) (hbc : op b = op c) : (
homOfLE hab).op ≫ eqToHom hbc = (homOfLE ((le_of_eq (op_injective hbc.symm)).tra
ns hab)).op
参数：hab : b <= a；hbc : op b = op c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homOfLE_op_comp_eqToHom {a b c : X} (hab : b ≤ a) (hbc : op b = op c) :
    (homOfLE hab).op ≫ eqToHom hbc = (homOfLE ((le_of_eq (op_injective hbc.symm)).trans hab)).op :=
  rfl

@[simp, reassoc]
/-
**CategoryTheory.eqToHom_comp_homOfLE_op** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：eqToHom_comp_homOfLE_op {a b c : X} (hab : op a = op b) (hbc : c <= b) : e
qToHom hab ≫ (homOfLE hbc).op = (homOfLE (hbc.trans (le_of_eq (op_injective hab.
symm)))).op
参数：hab : op a = op b；hbc : c <= b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eqToHom_comp_homOfLE_op {a b c : X} (hab : op a = op b) (hbc : c ≤ b) :
    eqToHom hab ≫ (homOfLE hbc).op = (homOfLE (hbc.trans (le_of_eq (op_injective hab.symm)))).op :=
  rfl

/-- Construct a morphism in the opposite of a preorder category from an inequality. -/
/-
**CategoryTheory.opHomOfLE** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：opHomOfLE {x y : Xᵒᵖ} (h : unop x <= unop y) : y ⟶ x
参数：h : unop x <= unop y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a morphism in the opposite of a preorder category from an inequality.
-/
def opHomOfLE {x y : Xᵒᵖ} (h : unop x ≤ unop y) : y ⟶ x :=
  (homOfLE h).op
/-
**CategoryTheory.le_of_op_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：le_of_op_hom {x y : Xᵒᵖ} (h : x ⟶ y) : unop y <= unop x
参数：h : x ⟶ y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_of_op_hom {x y : Xᵒᵖ} (h : x ⟶ y) : unop y ≤ unop x :=
  h.unop.le
/-
**CategoryTheory.uniqueToTop** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：uniqueToTop [OrderTop X] {x : X} : Unique (x ⟶ ⊤) where default
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueToTop [OrderTop X] {x : X} : Unique (x ⟶ ⊤) where
  default := homOfLE le_top
  uniq := fun a => by rfl
/-
**CategoryTheory.uniqueFromBot** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：uniqueFromBot [OrderBot X] {x : X} : Unique (⊥ ⟶ x) where default
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueFromBot [OrderBot X] {x : X} : Unique (⊥ ⟶ x) where
  default := homOfLE bot_le
  uniq := fun a => by rfl

variable (X) in
/-- The equivalence of categories from the order dual of a preordered type `X`
to the opposite category of the preorder `X`. -/
@[simps]
/-
**CategoryTheory.orderDualEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`
。
形式化陈述：orderDualEquivalence : Xᵒᵈ ≌ Xᵒᵖ where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of categories from the order dual of a preordered type `X`
to the opposite category of the preorder `X`.
-/
def orderDualEquivalence : Xᵒᵈ ≌ Xᵒᵖ where
  functor :=
    { obj := fun x => op (OrderDual.ofDual x)
      map := fun f => (homOfLE (leOfHom f)).op }
  inverse :=
    { obj := fun x => OrderDual.toDual x.unop
      map := fun f => (homOfLE (leOfHom f.unop)) }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end CategoryTheory

section

open CategoryTheory

variable {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]

/-- A monotone function between preorders induces a functor between the associated categories. -/
/-
**Monotone.functor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Monotone.functor {f : X -> Y} (h : Monotone f) : X ⥤ Y where obj
参数：h : Monotone f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monotone function between preorders induces a functor between the associated c
ategories.
-/
def Monotone.functor {f : X → Y} (h : Monotone f) : X ⥤ Y where
  obj := f
  map g := CategoryTheory.homOfLE (h g.le)

@[simp]
/-
**Monotone.functor_obj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.functor_obj {f : X -> Y} (h : Monotone f) : h.functor.obj = f
参数：h : Monotone f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Monotone.functor_obj {f : X → Y} (h : Monotone f) : h.functor.obj = f :=
  rfl

-- Faithfulness is automatic because preorder categories are thin
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ↪o Y) : f.monotone.functor.Full where
  map_surjective h := ⟨homOfLE (f.map_rel_iff.1 h.le), rfl⟩

/-- The equivalence of categories `X ≌ Y` induced by `e : X ≃o Y`. -/
@[simps]
/-
**OrderIso.equivalence** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderIso.equivalence (e : X ≃o Y) : X ≌ Y where functor
参数：e : X ≃o Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (e : α ≃o β), Monotone ⇑e

--- 原说明 ---
The equivalence of categories `X ≌ Y` induced by `e : X ≃o Y`.
-/
def OrderIso.equivalence (e : X ≃o Y) : X ≌ Y where
  functor := e.monotone.functor
  inverse := e.symm.monotone.functor
  unitIso := NatIso.ofComponents (fun _ ↦ eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun _ ↦ eqToIso (by simp))

end

section Preorder

variable {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]

namespace CategoryTheory.Functor

/-- A functor between preorder categories is monotone. -/
@[gcongr, mono]
/-
**CategoryTheory.Functor.monotone** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：monotone (f : X ⥤ Y) : Monotone f.obj
参数：f : X ⥤ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor between preorder categories is monotone.
-/
theorem monotone (f : X ⥤ Y) : Monotone f.obj := fun _ _ hxy => (f.map hxy.hom).le

/-- A functor `X ⥤ Y` between preorder categories as an `OrderHom`. -/
@[simps!]
/-
**CategoryTheory.Functor.toOrderHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：toOrderHom (F : X ⥤ Y) : X ->o Y where toFun
参数：F : X ⥤ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.monotone`：monotone (f : X ⥤ Y) : Monotone f.obj

--- 原说明 ---
A functor `X ⥤ Y` between preorder categories as an `OrderHom`.
-/
def toOrderHom (F : X ⥤ Y) : X →o Y where
  toFun := F.obj
  monotone' := F.monotone

end CategoryTheory.Functor

namespace OrderHom

open CategoryTheory

/-- An `OrderHom` as a functor `X ⥤ Y` between preorder categories. -/
/-
**OrderHom.toFunctor** 是 Mathlib 中的一个缩写定义，位于命名空间 `OrderHom`。
形式化陈述：toFunctor (f : X ->o Y) : X ⥤ Y
参数：f : X ->o Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f

--- 原说明 ---
An `OrderHom` as a functor `X ⥤ Y` between preorder categories.
-/
abbrev toFunctor (f : X →o Y) : X ⥤ Y := f.monotone.functor

/-- The equivalence between `X →o Y` and the type of functors `X ⥤ Y` between preorder categories
`X` and `Y`. -/
@[simps]
/-
**OrderHom.equivFunctor** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：equivFunctor : (X ->o Y) ≃ (X ⥤ Y) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `X →o Y` and the type of functors `X ⥤ Y` between preord
er categories
`X` and `Y`.
-/
def equivFunctor : (X →o Y) ≃ (X ⥤ Y) where
  toFun := toFunctor
  invFun F := F.toOrderHom

/-- The categorical equivalence between the category of monotone functions `X →o Y` and the category
of functors `X ⥤ Y`, where `X` and `Y` are preorder categories. -/
@[simps! functor_obj_obj inverse_obj unitIso_hom_app unitIso_inv_app counitIso_inv_app_app
  counitIso_hom_app_app]
/-
**OrderHom.equivalenceFunctor** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：equivalenceFunctor : (X ->o Y) ≌ (X ⥤ Y) where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def equivalenceFunctor : (X →o Y) ≌ (X ⥤ Y) where
  functor :=
    { obj f := f.toFunctor
      map f := { app x := homOfLE <| leOfHom f x } }
  inverse :=
    { obj F := F.toOrderHom
      map f := homOfLE fun x ↦ leOfHom <| f.app x }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end OrderHom

end Preorder

section PartialOrder

namespace CategoryTheory

variable {X : Type u} {Y : Type v} [PartialOrder X] [PartialOrder Y]

/-
**CategoryTheory.Iso.to_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：∀ {X : Type u} [inst : PartialOrder X] {x y : X} (f : x ≅ y), x = y
参数：f : x ≅ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
theorem Iso.to_eq {x y : X} (f : x ≅ y) : x = y :=
  le_antisymm f.hom.le f.inv.le

/-- A categorical equivalence between partial orders is just an order isomorphism. -/
/-
**CategoryTheory.Equivalence.toOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Equivalence`。
形式化陈述：{X : Type u} → {Y : Type v} → [inst : PartialOrder X] → [inst_1 : PartialO
rder Y] → (X ≌ Y) → X ≃o Y
参数：X ≌ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A categorical equivalence between partial orders is just an order isomorphism.
-/
def Equivalence.toOrderIso (e : X ≌ Y) : X ≃o Y where
  toFun := e.functor.obj
  invFun := e.inverse.obj
  left_inv a := (e.unitIso.app a).to_eq.symm
  right_inv b := (e.counitIso.app b).to_eq
  map_rel_iff' {a a'} :=
    ⟨fun h =>
      ((Equivalence.unit e).app a ≫ e.inverse.map h.hom ≫ (Equivalence.unitInv e).app a').le,
      fun h : a ≤ a' => (e.functor.map h.hom).le⟩

-- `@[simps]` on `Equivalence.toOrderIso` produces lemmas that fail the `simpNF` linter,
-- so we provide them by hand:
@[simp]
/-
**CategoryTheory.Equivalence.toOrderIso_apply** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Equivalence`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : PartialOrder X] [inst_1 : PartialOrder
 Y] (e : X ≌ Y) (x : X),   e.toOrderIso x = e.functor.obj x
参数：e : X ≌ Y；x : X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Equivalence.toOrderIso_apply (e : X ≌ Y) (x : X) : e.toOrderIso x = e.functor.obj x :=
  rfl

@[simp]
/-
**CategoryTheory.Equivalence.toOrderIso_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Equivalence`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : PartialOrder X] [inst_1 : PartialOrder
 Y] (e : X ≌ Y) (y : Y),   e.toOrderIso.symm y = e.inverse.obj y
参数：e : X ≌ Y；y : Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Equivalence.toOrderIso_symm_apply (e : X ≌ Y) (y : Y) :
    e.toOrderIso.symm y = e.inverse.obj y :=
  rfl

end CategoryTheory

end PartialOrder

open CategoryTheory

/-
**PartialOrder.isIso_iff_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PartialOrder.isIso_iff_eq {X : Type u} [PartialOrder X] {a b : X} (f : a ⟶
 b) : IsIso f ↔ a = b
参数：f : a ⟶ b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.to_eq`：∀ {X : Type u} [inst : PartialOrder X] {x y : 
X} (f : x ≅ y), x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma PartialOrder.isIso_iff_eq {X : Type u} [PartialOrder X]
    {a b : X} (f : a ⟶ b) : IsIso f ↔ a = b := by
  constructor
  · intro _
    exact (asIso f).to_eq
  · rintro rfl
    rw [Subsingleton.elim f (𝟙 _)]
    infer_instance
