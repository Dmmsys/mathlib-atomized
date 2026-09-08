/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.SetTheory.Cardinal.Free

import Mathlib.Algebra.MonoidAlgebra.Cardinal

/-!
# Cardinality of free algebras

This file contains some results about the cardinality of `FreeAlgebra`,
parallel to that of `MvPolynomial`.
-/

public section

universe u v

variable (R : Type u) [CommSemiring R]

open Cardinal

namespace FreeAlgebra

variable (X : Type v)

@[simp]
/-
**FreeAlgebra.cardinalMk_eq_max_lift** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
形式化陈述：cardinalMk_eq_max_lift [Nonempty X] [Nontrivial R] : #(FreeAlgebra R X) = 
Cardinal.lift.{v} #R ⊔ Cardinal.lift.{u} #X ⊔ ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_freeMonoid`：mk_freeMonoid [Nonempty α] : #(FreeMonoid α) = m
ax #α ℵ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
· 使用引理 `MonoidAlgebra.cardinalMk_eq_max_lift_of_infinite`：cardinalMk_eq_max_lift
_of_infinite [Infinite M'] [Nontrivial R] : #R[M'] = max (lift.{v} #R) (lift.{u}
 #M')
· 使用定理 `instInfiniteFreeMonoidOfNonempty`：∀ (α : Type u) [Nonempty α], Infinite 
(FreeMonoid α)
· 使用定理 `Cardinal.lift_max`：lift_max {a b : Cardinal} : lift.{u, v} (max a b) = m
ax (lift.{u, v} a) (lift.{u, v} b)
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
-/
theorem cardinalMk_eq_max_lift [Nonempty X] [Nontrivial R] :
    #(FreeAlgebra R X) = Cardinal.lift.{v} #R ⊔ Cardinal.lift.{u} #X ⊔ ℵ₀ := by
  have hX := mk_freeMonoid X
  rw [equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq,
    MonoidAlgebra.cardinalMk_eq_max_lift_of_infinite, hX, lift_max, lift_aleph0, sup_assoc]

@[simp]
/-
**FreeAlgebra.cardinalMk_eq_lift** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
形式化陈述：cardinalMk_eq_lift [IsEmpty X] : #(FreeAlgebra R X) = Cardinal.lift.{v} #R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
· 使用引理 `MonoidAlgebra.cardinalMk_eq_lift_of_fintype`：cardinalMk_eq_lift_of_finty
pe [Fintype M'] : #R[M'] = lift.{v} #R ^ card M'
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cardinalMk_eq_lift [IsEmpty X] : #(FreeAlgebra R X) = Cardinal.lift.{v} #R := by
  simp [equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq,
    MonoidAlgebra.cardinalMk_eq_lift_of_fintype]

@[nontriviality]
/-
**FreeAlgebra.cardinalMk_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
形式化陈述：cardinalMk_eq_one [Subsingleton R] : #(FreeAlgebra R X) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
· 使用定理 `Cardinal.mk_eq_one`：mk_eq_one (α : Type u) [Subsingleton α] [Nonempty α]
 : #α = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem cardinalMk_eq_one [Subsingleton R] : #(FreeAlgebra R X) = 1 := by
  rw [equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq, mk_eq_one]
/-
**FreeAlgebra.cardinalMk_le_max_lift** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
形式化陈述：cardinalMk_le_max_lift : #(FreeAlgebra R X) <= Cardinal.lift.{v} #R ⊔ Card
inal.lift.{u} #X ⊔ ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `FreeAlgebra.cardinalMk_eq_one`：cardinalMk_eq_one [Subsingleton R] : #(Fr
eeAlgebra R X) = 1
· 使用定理 `le_max_of_le_right`：le_max_of_le_right : a <= c -> a <= max b c
· 使用定理 `Cardinal.one_le_aleph0`：one_le_aleph0 : 1 <= ℵ₀
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `FreeAlgebra.cardinalMk_eq_lift`：cardinalMk_eq_lift [IsEmpty X] : #(FreeA
lgebra R X) = Cardinal.lift.{v} #R
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `FreeAlgebra.cardinalMk_eq_max_lift`：cardinalMk_eq_max_lift [Nonempty X] 
[Nontrivial R] : #(FreeAlgebra R X) = Cardinal.lift.{v} #R ⊔ Cardinal.lift.{u} #
X ⊔ ℵ₀
-/
theorem cardinalMk_le_max_lift :
    #(FreeAlgebra R X) ≤ Cardinal.lift.{v} #R ⊔ Cardinal.lift.{u} #X ⊔ ℵ₀ := by
  cases subsingleton_or_nontrivial R
  · exact (cardinalMk_eq_one R X).trans_le (le_max_of_le_right one_le_aleph0)
  cases isEmpty_or_nonempty X
  · exact (cardinalMk_eq_lift R X).trans_le (le_max_of_le_left <| le_max_left _ _)
  · exact (cardinalMk_eq_max_lift R X).le

variable (X : Type u)
/-
**FreeAlgebra.cardinalMk_eq_max** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
形式化陈述：cardinalMk_eq_max [Nonempty X] [Nontrivial R] : #(FreeAlgebra R X) = #R ⊔ 
#X ⊔ ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeAlgebra.cardinalMk_eq_max_lift`：cardinalMk_eq_max_lift [Nonempty X] 
[Nontrivial R] : #(FreeAlgebra R X) = Cardinal.lift.{v} #R ⊔ Cardinal.lift.{u} #
X ⊔ ℵ₀
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cardinalMk_eq_max [Nonempty X] [Nontrivial R] : #(FreeAlgebra R X) = #R ⊔ #X ⊔ ℵ₀ := by
  simp
/-
**FreeAlgebra.cardinalMk_eq** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
形式化陈述：cardinalMk_eq [IsEmpty X] : #(FreeAlgebra R X) = #R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeAlgebra.cardinalMk_eq_lift`：cardinalMk_eq_lift [IsEmpty X] : #(FreeA
lgebra R X) = Cardinal.lift.{v} #R
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cardinalMk_eq [IsEmpty X] : #(FreeAlgebra R X) = #R := by
  simp
/-
**FreeAlgebra.cardinalMk_le_max** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
形式化陈述：cardinalMk_le_max : #(FreeAlgebra R X) <= #R ⊔ #X ⊔ ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `FreeAlgebra.cardinalMk_le_max_lift`：cardinalMk_le_max_lift : #(FreeAlgeb
ra R X) <= Cardinal.lift.{v} #R ⊔ Cardinal.lift.{u} #X ⊔ ℵ₀
-/
theorem cardinalMk_le_max : #(FreeAlgebra R X) ≤ #R ⊔ #X ⊔ ℵ₀ := by
  simpa using cardinalMk_le_max_lift R X

end FreeAlgebra

namespace Algebra

/-
**Algebra.lift_cardinalMk_adjoin_le** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：lift_cardinalMk_adjoin_le {A : Type v} [Semiring A] [Algebra R A] (s : Set
 A) : lift.{u} #(adjoin R s) <= lift.{v} #R ⊔ lift.{u} #s ⊔ ℵ₀
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_range_le_lift`：mk_range_le_lift {α : Type u} {β : Type v} {f
 : α -> β} : lift.{u} #(range f) <= lift.{v} #α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.adjoin_eq_range_freeAlgebra_lift`：∀ (R : Type u_1) [inst : CommS
emiring R] {A : Type u_3} [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : Set 
A),   Algebra.adjoin R s = ((F…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `FreeAlgebra.cardinalMk_le_max_lift`：cardinalMk_le_max_lift : #(FreeAlgeb
ra R X) <= Cardinal.lift.{v} #R ⊔ Cardinal.lift.{u} #X ⊔ ℵ₀
-/
theorem lift_cardinalMk_adjoin_le {A : Type v} [Semiring A] [Algebra R A] (s : Set A) :
    lift.{u} #(adjoin R s) ≤ lift.{v} #R ⊔ lift.{u} #s ⊔ ℵ₀ := by
  have H := mk_range_le_lift (f := FreeAlgebra.lift R ((↑) : s → A))
  rw [lift_umax, lift_id'.{v, u}] at H
  rw [Algebra.adjoin_eq_range_freeAlgebra_lift]
  exact H.trans (FreeAlgebra.cardinalMk_le_max_lift R s)
/-
**Algebra.cardinalMk_adjoin_le** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：cardinalMk_adjoin_le {A : Type u} [Semiring A] [Algebra R A] (s : Set A) :
 #(adjoin R s) <= #R ⊔ #s ⊔ ℵ₀
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.lift_cardinalMk_adjoin_le`：lift_cardinalMk_adjoin_le {A : Type v
} [Semiring A] [Algebra R A] (s : Set A) : lift.{u} #(adjoin R s) <= lift.{v} #R
 ⊔ lift.{u} #s ⊔ ℵ₀
-/
theorem cardinalMk_adjoin_le {A : Type u} [Semiring A] [Algebra R A] (s : Set A) :
    #(adjoin R s) ≤ #R ⊔ #s ⊔ ℵ₀ := by
  simpa using lift_cardinalMk_adjoin_le R s

end Algebra

