/-
Copyright (c) 2021 Chris Hughes, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Cardinal
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Data.Finsupp.Fintype
public import Mathlib.SetTheory.Cardinal.Arithmetic

import Mathlib.Algebra.MonoidAlgebra.Cardinal

/-!
# Cardinality of Multivariate Polynomial Ring

The main result in this file is `MvPolynomial.cardinalMk_le_max`, which says that
the cardinality of `MvPolynomial σ R` is bounded above by the maximum of `#R`, `#σ`
and `ℵ₀`.
-/

public section


universe u v

open Cardinal

namespace MvPolynomial

section TwoUniverses

variable {σ : Type u} {R : Type v} [CommSemiring R]

-- We want this to have higher priority than `AddMonoidAlgebra.cardinalMk_eq_max_lift_of_infinite`.
@[simp high]
/-
**MvPolynomial.cardinalMk_eq_max_lift** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：cardinalMk_eq_max_lift [Nonempty σ] [Nontrivial R] : #(MvPolynomial σ R) =
 lift.{u} #R ⊔ lift.{v} #σ ⊔ ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.cardinalMk_eq_max_lift_of_infinite`：∀ (R : Type u) (M' 
: Type v) [inst : Semiring R] [Infinite M'] [Nontrivial R],   Cardinal.mk (AddMo
noidAlgebra R M') =     max (Cardinal.lif…
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Cardinal.mk_finsupp_lift_of_infinite'`：mk_finsupp_lift_of_infinite' (α :
 Type u) (β : Type v) [Nonempty α] [Zero β] [Infinite β] : #(α ->₀ β) = max (lif
t.{v} #α) (lift.{u} #β)
· 使用定理 `Cardinal.lift_uzero`：lift_uzero (a : Cardinal.{u}) : lift.{0} a = a
· 使用定理 `Cardinal.mk_eq_aleph0`：mk_eq_aleph0 (α : Type*) [Countable α] [Infinite 
α] : #α = ℵ₀
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `Cardinal.lift_max`：lift_max {a b : Cardinal} : lift.{u, v} (max a b) = m
ax (lift.{u, v} a) (lift.{u, v} b)
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cardinalMk_eq_max_lift [Nonempty σ] [Nontrivial R] :
    #(MvPolynomial σ R) = lift.{u} #R ⊔ lift.{v} #σ ⊔ ℵ₀ := by simp [sup_assoc]

-- We want this to have higher priority than `AddMonoidAlgebra.cardinalMk_eq_lift_of_fintype`.
@[simp high]
/-
**MvPolynomial.cardinalMk_eq_lift** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：cardinalMk_eq_lift [IsEmpty σ] : #(MvPolynomial σ R) = lift.{u} #R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.cardinalMk_eq_lift_of_fintype`：∀ (R : Type u) (M' : Typ
e v) [inst : Semiring R] [inst_1 : Fintype M'],   Cardinal.mk (AddMonoidAlgebra 
R M') = Cardinal.lift.{v, u} (Cardin…
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cardinalMk_eq_lift [IsEmpty σ] : #(MvPolynomial σ R) = lift.{u} #R := by simp

@[nontriviality]
/-
**MvPolynomial.cardinalMk_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：cardinalMk_eq_one [Subsingleton R] : #(MvPolynomial σ R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_eq_one`：mk_eq_one (α : Type u) [Subsingleton α] [Nonempty α]
 : #α = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem cardinalMk_eq_one [Subsingleton R] : #(MvPolynomial σ R) = 1 := mk_eq_one _


/-- The cardinality of the multivariate polynomial ring, `MvPolynomial σ R` is at most the maximum
of `#R`, `#σ` and `ℵ₀`.

See `cardinalMk_le_max` for the universe monomorphic version. -/
/-
**MvPolynomial.cardinalMk_le_max_lift** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：cardinalMk_le_max_lift {σ : Type u} {R : Type v} [CommSemiring R] : #(MvPo
lynomial σ R) <= lift.{u} #R ⊔ lift.{v} #σ ⊔ ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `MvPolynomial.cardinalMk_eq_lift`：cardinalMk_eq_lift [IsEmpty σ] : #(MvPo
lynomial σ R) = lift.{u} #R
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
· 使用定理 `Cardinal.lift_zero`：lift_zero : lift 0 = 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `MvPolynomial.cardinalMk_eq_max_lift`：cardinalMk_eq_max_lift [Nonempty σ]
 [Nontrivial R] : #(MvPolynomial σ R) = lift.{u} #R ⊔ lift.{v} #σ ⊔ ℵ₀

--- 原说明 ---
The cardinality of the multivariate polynomial ring, `MvPolynomial σ R` is at mo
st the maximum
of `#R`, `#σ` and `ℵ₀`.

See `cardinalMk_le_max` for the universe monomorphic version.
-/
theorem cardinalMk_le_max_lift {σ : Type u} {R : Type v} [CommSemiring R] :
    #(MvPolynomial σ R) ≤ lift.{u} #R ⊔ lift.{v} #σ ⊔ ℵ₀ := by
  nontriviality R; cases isEmpty_or_nonempty σ <;> simp

end TwoUniverses

variable {σ R : Type u} [CommSemiring R]

/-
**MvPolynomial.cardinalMk_eq_max** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：cardinalMk_eq_max [Nonempty σ] [Nontrivial R] : #(MvPolynomial σ R) = #R ⊔
 #σ ⊔ ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.cardinalMk_eq_max_lift`：cardinalMk_eq_max_lift [Nonempty σ]
 [Nontrivial R] : #(MvPolynomial σ R) = lift.{u} #R ⊔ lift.{v} #σ ⊔ ℵ₀
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cardinalMk_eq_max [Nonempty σ] [Nontrivial R] : #(MvPolynomial σ R) = #R ⊔ #σ ⊔ ℵ₀ := by
  simp [sup_assoc]
/-
**MvPolynomial.cardinalMk_eq** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：cardinalMk_eq [IsEmpty σ] : #(MvPolynomial σ R) = #R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.cardinalMk_eq_lift`：cardinalMk_eq_lift [IsEmpty σ] : #(MvPo
lynomial σ R) = lift.{u} #R
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cardinalMk_eq [IsEmpty σ] : #(MvPolynomial σ R) = #R := by simp

/-- The cardinality of the multivariate polynomial ring, `MvPolynomial σ R` is at most the maximum
of `#R`, `#σ` and `ℵ₀`.

See `cardinalMk_le_max_lift` for the universe polymorphic version. -/
/-
**MvPolynomial.cardinalMk_le_max** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：cardinalMk_le_max : #(MvPolynomial σ R) <= #R ⊔ #σ ⊔ ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MvPolynomial.cardinalMk_le_max_lift`：cardinalMk_le_max_lift {σ : Type u}
 {R : Type v} [CommSemiring R] : #(MvPolynomial σ R) <= lift.{u} #R ⊔ lift.{v} #
σ ⊔ ℵ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
The cardinality of the multivariate polynomial ring, `MvPolynomial σ R` is at mo
st the maximum
of `#R`, `#σ` and `ℵ₀`.

See `cardinalMk_le_max_lift` for the universe polymorphic version.
-/
theorem cardinalMk_le_max : #(MvPolynomial σ R) ≤ #R ⊔ #σ ⊔ ℵ₀ :=
  cardinalMk_le_max_lift.trans <| by rw [lift_id, lift_id]

end MvPolynomial

