/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Monoid.Basic
public import Mathlib.Algebra.Order.Ring.Defs

/-!
# Pulling back ordered rings along injective maps
-/

public section

variable {R S : Type*}

namespace Function.Injective
variable [Semiring R] [PartialOrder R]

/-- Pullback an `IsOrderedRing` under an injective map. -/
/-
**Function.Injective.isOrderedRing** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective
`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [IsOrderedRing R] [inst_3 : Semiring S]   [inst_4 : PartialOrder S] (f : S →
 R),   f 0 = 0 →     f 1 = 1 →       (∀ (x y : S), f (x + y) = f x + f y) →     
    (∀ (x y : S), f (x * y) = f x * f y) → (∀ {x y : S}, f x ≤ f y ↔ x ≤ y) → Is
OrderedRing S
参数：f : S → R；∀ (x y : S), f (x + y) = f x + f y；∀ (x y : S), f (x * y) = f x * f
 y；∀ {x y : S}, f x ≤ f y ↔ x ≤ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isOrderedAddMonoid`：∀ {α : Type u} {β : Type u_1} [in
st : AddCommMonoid α] [inst_1 : Preorder α] [IsOrderedAddMonoid α]   [inst_3 : A
ddCommMonoid β] [inst_4 : P…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R

--- 原说明 ---
Pullback an `IsOrderedRing` under an injective map.
-/
protected lemma isOrderedRing [IsOrderedRing R] [Semiring S] [PartialOrder S]
    (f : S → R) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) :
    IsOrderedRing S where
  __ := Function.Injective.isOrderedAddMonoid f add le
  zero_le_one := by simp only [← le, zero, one, zero_le_one]
  mul_le_mul_of_nonneg_left a ha b c hbc := by
    rw [← le, mul, mul]; refine mul_le_mul_of_nonneg_left (le.2 hbc) ?_; rwa [← zero, le]
  mul_le_mul_of_nonneg_right a ha b c hbc := by
    rw [← le, mul, mul]; refine mul_le_mul_of_nonneg_right (le.2 hbc) ?_; rwa [← zero, le]

/-- Pullback a `IsStrictOrderedRing` under an injective map. -/
/-
**Function.Injective.isStrictOrderedRing** 是 Mathlib 中的一个定理，位于命名空间 `Function.Inj
ective`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [IsStrictOrderedRing R]   [inst_3 : Semiring S] [inst_4 : PartialOrder S] (f
 : S → R),   f 0 = 0 →     f 1 = 1 →       (∀ (x y : S), f (x + y) = f x + f y) 
→         (∀ (x y : S), f (x * y) = f x * f y) →           (∀ {x y : S}, f x ≤ f
 y ↔ x ≤ y) → (∀ {x y : S}, f x < f y ↔ x < y) → IsStrictOrderedRing S
参数：f : S → R；∀ (x y : S), f (x + y) = f x + f y；∀ (x y : S), f (x * y) = f x * f
 y；∀ {x y : S}, f x ≤ f y ↔ x ≤ y；∀ {x y : S}, f x < f y ↔ x < y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isOrderedCancelAddMonoid`：∀ {α : Type u} {β : Type u_
1} [inst : AddCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α]  
 [inst_3 : AddCommMonoid β] [inst…
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `domain_nontrivial`：domain_nontrivial [Zero M₀'] [One M₀'] (f : M₀' -> M₀
) (zero : f 0 = 0) (one : f 1 = 1) : Nontrivial M₀'
· 使用定理 `IsStrictOrderedRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} {
inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], Nontrivial R
· 使用定理 `Function.Injective.isOrderedRing`：∀ {R : Type u_1} {S : Type u_2} [inst 
: Semiring R] [inst_1 : PartialOrder R] [IsOrderedRing R] [inst_3 : Semiring S] 
  [inst_4 : PartialOrd…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R

--- 原说明 ---
Pullback a `IsStrictOrderedRing` under an injective map.
-/
protected lemma isStrictOrderedRing [IsStrictOrderedRing R] [Semiring S] [PartialOrder S]
    (f : S → R) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y) :
    IsStrictOrderedRing S where
  __ := Function.Injective.isOrderedCancelAddMonoid f add le
  __ := domain_nontrivial f zero one
  __ := Function.Injective.isOrderedRing f zero one add mul le
  mul_lt_mul_of_pos_left a ha b c hbc := by
    rw [← lt, mul, mul]; refine mul_lt_mul_of_pos_left (lt.2 hbc) ?_; rwa [← zero, lt]
  mul_lt_mul_of_pos_right a ha b c hbc := by
    rw [← lt, mul, mul]; refine mul_lt_mul_of_pos_right (lt.2 hbc) ?_; rwa [← zero, lt]

end Function.Injective

