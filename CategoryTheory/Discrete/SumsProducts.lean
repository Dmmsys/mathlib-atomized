/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Sums.Basic
public import Mathlib.CategoryTheory.Products.Basic

/-! # Sums and products of discrete categories.

This file shows that binary products and binary sums of discrete categories
are also discrete, both in the form of explicit equivalences and through the
`IsDiscrete` typeclass.

## Main declarations

* `Discrete.productEquiv`: The equivalence of categories between `Discrete (J × K)`
  and `Discrete J × Discrete K`
* `Discrete.sumEquiv`: The equivalence of categories between `Discrete (J ⊕ K)`
  and `Discrete J ⊕ Discrete K`.
* `IsDiscrete.prod`: an `IsDiscrete` instance on the product of two discrete categories.
* `IsDiscrete.sum`: an `IsDiscrete` instance on the sum of two discrete categories.

-/

@[expose] public section

namespace CategoryTheory

namespace Discrete

/-- The discrete category on a product is equivalent to the product of the
discrete categories. -/
@[simps!]
/-
**CategoryTheory.Discrete.productEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Discrete`。
形式化陈述：productEquiv {J K : Type*} : Discrete (J × K) ≌ Discrete J × Discrete K wh
ere functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The discrete category on a product is equivalent to the product of the
discrete categories.
-/
def productEquiv {J K : Type*} : Discrete (J × K) ≌ Discrete J × Discrete K where
  functor := Discrete.functor <| fun ⟨j, k⟩ ↦ ⟨.mk j, .mk k⟩
  inverse := {
    obj := fun ⟨x, y⟩ ↦ .mk (⟨x.as, y.as⟩)
    map := fun ⟨f₁, f₂⟩ ↦ eqToHom (by discrete_cases; dsimp; rw [f₁, f₂]) }
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The discrete category on a sum is equivalent to the sum of the
discrete categories. -/
@[simps!]
/-
**CategoryTheory.Discrete.sumEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Dis
crete`。
形式化陈述：sumEquiv {J K : Type*} : Discrete (J oplus K) ≌ Discrete J oplus Discrete 
K where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The discrete category on a sum is equivalent to the sum of the
discrete categories.
-/
def sumEquiv {J K : Type*} : Discrete (J ⊕ K) ≌ Discrete J ⊕ Discrete K where
  functor := Discrete.functor <| fun t ↦
    match t with
    | .inl j => Sum.inl (Discrete.mk j)
    | .inr k => Sum.inr (Discrete.mk k)
  inverse := (Discrete.functor <| fun t ↦ Discrete.mk (Sum.inl t)).sum'
    (Discrete.functor <| fun t ↦ Discrete.mk (Sum.inr t))
  unitIso := NatIso.ofComponents (fun ⟨x⟩ ↦
    match x with
    | .inl x => Iso.refl _
    | .inr x => Iso.refl _)
  counitIso := Functor.sumIsoExt
    (Discrete.natIso <| fun _ ↦ Iso.refl _)
    (Discrete.natIso <| fun _ ↦ Iso.refl _)

end Discrete

namespace IsDiscrete

variable (C C' : Type*) [Category* C] [Category* C'] (D : Type*) [Category* D]
  [IsDiscrete C] [IsDiscrete C'] [IsDiscrete D]

/-- A product of discrete categories is discrete. -/
/-
**CategoryTheory.IsDiscrete.prod** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.IsDis
crete`。
形式化陈述：prod : IsDiscrete (C × D) where subsingleton x y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `CategoryTheory.IsDiscrete.eq_of_hom`：∀ {C : Type u_1} {inst : CategoryTh
eory.Category.{v_1, u_1} C} [self : CategoryTheory.IsDiscrete C] {X Y : C}   (f 
: X ⟶ Y), X = Y

--- 原说明 ---
A product of discrete categories is discrete.
-/
instance prod : IsDiscrete (C × D) where
  subsingleton x y := inferInstanceAs (Subsingleton ((x.1 ⟶ y.1) × (x.2 ⟶ y.2)))
  eq_of_hom f := Prod.ext (IsDiscrete.eq_of_hom f.1) (IsDiscrete.eq_of_hom f.2)

/-- A sum of discrete categories is discrete. -/
/-
**CategoryTheory.IsDiscrete.sum** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.IsDisc
rete`。
形式化陈述：sum : IsDiscrete (C oplus C') where subsingleton x y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.allEq`：∀ {α : Sort u} [self : Subsingleton α] (a b : α), a 
= b
· 使用定理 `CategoryTheory.IsDiscrete.subsingleton`：∀ {C : Type u_1} {inst : Categor
yTheory.Category.{v_1, u_1} C} [self : CategoryTheory.IsDiscrete C] (X Y : C),  
 Subsingleton (X ⟶ Y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `CategoryTheory.IsDiscrete.eq_of_hom`：∀ {C : Type u_1} {inst : CategoryTh
eory.Category.{v_1, u_1} C} [self : CategoryTheory.IsDiscrete C] {X Y : C}   (f 
: X ⟶ Y), X = Y

--- 原说明 ---
A sum of discrete categories is discrete.
-/
instance sum : IsDiscrete (C ⊕ C') where
  subsingleton x y :=
    { allEq f g := by
        cases f <;> cases g
        · case inl x y f g => rw [((by assumption : IsDiscrete C).subsingleton x y).allEq f g]
        · case inr x y f g => rw [((by assumption : IsDiscrete C').subsingleton x y).allEq f g] }
  eq_of_hom {x y} f := by
    cases f with
    | inl x y f => rw [(by assumption : IsDiscrete C).eq_of_hom f]
    | inr x y f => rw [(by assumption : IsDiscrete C').eq_of_hom f]

end CategoryTheory.IsDiscrete

