/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
module

public import Mathlib.Algebra.Ring.Semiconj
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Data.Bracket

/-!
# Semirings and rings

This file gives lemmas about semirings, rings and domains.
This is analogous to `Mathlib/Algebra/Group/Basic.lean`,
the difference being that the former is about `+` and `*` separately, while
the present file is about their interaction.

For the definitions of semirings and rings see `Mathlib/Algebra/Ring/Defs.lean`.

-/

@[expose] public section


universe u

variable {R : Type u}

open Function

namespace Commute

@[simp]
/-
**Commute.add_right** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：add_right [Distrib R] {a b c : R} : Commute a b -> Commute a c -> Commute 
a (b + c)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.add_right`：add_right [Distrib R] {a x y x' y' : R} (h : Semic
onjBy a x y) (h' : SemiconjBy a x' y') : SemiconjBy a (x + x') (y + y')
-/
theorem add_right [Distrib R] {a b c : R} : Commute a b → Commute a c → Commute a (b + c) :=
  SemiconjBy.add_right
-- for some reason mathport expected `Semiring` instead of `Distrib`?

@[simp]
/-
**Commute.add_left** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：add_left [Distrib R] {a b c : R} : Commute a c -> Commute b c -> Commute (
a + b) c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.add_left`：add_left [Distrib R] {a b x y : R} (ha : SemiconjBy
 a x y) (hb : SemiconjBy b x y) : SemiconjBy (a + b) x y
-/
theorem add_left [Distrib R] {a b c : R} : Commute a c → Commute b c → Commute (a + b) c :=
  SemiconjBy.add_left
-- for some reason mathport expected `Semiring` instead of `Distrib`?

/-- Representation of a difference of two squares of commuting elements as a product. -/
/-
**Commute.mul_self_sub_mul_self_eq** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：mul_self_sub_mul_self_eq [NonUnitalNonAssocRing R] {a b : R} (h : Commute 
a b) : a * a - b * b = (a + b) * (a - b)
参数：h : Commute a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c

--- 原说明 ---
Representation of a difference of two squares of commuting elements as a product
.
-/
theorem mul_self_sub_mul_self_eq [NonUnitalNonAssocRing R] {a b : R} (h : Commute a b) :
    a * a - b * b = (a + b) * (a - b) := by
  rw [add_mul, mul_sub, mul_sub, h.eq, sub_add_sub_cancel]
/-
**Commute.mul_self_sub_mul_self_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：mul_self_sub_mul_self_eq' [NonUnitalNonAssocRing R] {a b : R} (h : Commute
 a b) : a * a - b * b = (a - b) * (a + b)
参数：h : Commute a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
-/
theorem mul_self_sub_mul_self_eq' [NonUnitalNonAssocRing R] {a b : R} (h : Commute a b) :
    a * a - b * b = (a - b) * (a + b) := by
  rw [mul_add, sub_mul, sub_mul, h.eq, sub_add_sub_cancel]
/-
**Commute.mul_self_eq_mul_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：mul_self_eq_mul_self_iff [NonUnitalNonAssocRing R] [NoZeroDivisors R] {a b
 : R} (h : Commute a b) : a * a = b * b ↔ a = b ∨ a = -b
参数：h : Commute a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Commute.mul_self_sub_mul_self_eq`：mul_self_sub_mul_self_eq [NonUnitalNon
AssocRing R] {a b : R} (h : Commute a b) : a * a - b * b = (a + b) * (a - b)
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `add_eq_zero_iff_eq_neg`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ a = -b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_self_eq_mul_self_iff [NonUnitalNonAssocRing R] [NoZeroDivisors R] {a b : R}
    (h : Commute a b) : a * a = b * b ↔ a = b ∨ a = -b := by
  rw [← sub_eq_zero, h.mul_self_sub_mul_self_eq, mul_eq_zero, or_comm, sub_eq_zero,
    add_eq_zero_iff_eq_neg]

section

variable [Mul R] [HasDistribNeg R] {a b : R}

/-
**Commute.neg_right** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：neg_right : Commute a b -> Commute a (-b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.neg_right`：neg_right (h : SemiconjBy a x y) : SemiconjBy a (-
x) (-y)
-/
theorem neg_right : Commute a b → Commute a (-b) :=
  SemiconjBy.neg_right

@[simp]
/-
**Commute.neg_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：neg_right_iff : Commute a (-b) ↔ Commute a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.neg_right_iff`：neg_right_iff : SemiconjBy a (-x) (-y) ↔ Semic
onjBy a x y
-/
theorem neg_right_iff : Commute a (-b) ↔ Commute a b :=
  SemiconjBy.neg_right_iff
/-
**Commute.neg_left** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：neg_left : Commute a b -> Commute (-a) b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.neg_left`：neg_left (h : SemiconjBy a x y) : SemiconjBy (-a) x
 y
-/
theorem neg_left : Commute a b → Commute (-a) b :=
  SemiconjBy.neg_left

@[simp]
/-
**Commute.neg_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：neg_left_iff : Commute (-a) b ↔ Commute a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.neg_left_iff`：neg_left_iff : SemiconjBy (-a) x y ↔ SemiconjBy
 a x y
-/
theorem neg_left_iff : Commute (-a) b ↔ Commute a b :=
  SemiconjBy.neg_left_iff

end

section

variable [MulOneClass R] [HasDistribNeg R]

/-
**Commute.neg_one_right** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：neg_one_right (a : R) : Commute a (-1)
参数：a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.neg_one_right`：neg_one_right (a : R) : SemiconjBy a (-1) (-1)
-/
theorem neg_one_right (a : R) : Commute a (-1) :=
  SemiconjBy.neg_one_right a
/-
**Commute.neg_one_left** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：neg_one_left (a : R) : Commute (-1) a
参数：a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.neg_one_left`：neg_one_left (x : R) : SemiconjBy (-1) x x
-/
theorem neg_one_left (a : R) : Commute (-1) a :=
  SemiconjBy.neg_one_left a

end

section

variable [NonUnitalNonAssocRing R] {a b c : R}

@[simp]
/-
**Commute.sub_right** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：sub_right : Commute a b -> Commute a c -> Commute a (b - c)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.sub_right`：sub_right (h : SemiconjBy a x y) (h' : SemiconjBy 
a x' y') : SemiconjBy a (x - x') (y - y')
-/
theorem sub_right : Commute a b → Commute a c → Commute a (b - c) :=
  SemiconjBy.sub_right

@[simp]
/-
**Commute.sub_left** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：sub_left : Commute a c -> Commute b c -> Commute (a - b) c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.sub_left`：sub_left (ha : SemiconjBy a x y) (hb : SemiconjBy b
 x y) : SemiconjBy (a - b) x y
-/
theorem sub_left : Commute a c → Commute b c → Commute (a - b) c :=
  SemiconjBy.sub_left

end

section Semiring

variable [Semiring R]

/-
**Commute.add_sq** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {a b : R}, Commute a b → (a + b) ^ 2 = 
a ^ 2 + 2 * a * b + b ^ 2
参数：a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma add_sq {a b : R} (h : Commute a b) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  simp [sq, add_mul, mul_add, two_mul, h.eq, add_assoc]

end Semiring

section Ring
variable [Ring R] {a b : R}

/-
**Commute.sq_sub_sq** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {a b : R}, Commute a b → a ^ 2 - b ^ 2 = (a
 + b) * (a - b)
参数：a + b；a - b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Commute.mul_self_sub_mul_self_eq`：mul_self_sub_mul_self_eq [NonUnitalNon
AssocRing R] {a b : R} (h : Commute a b) : a * a - b * b = (a + b) * (a - b)
-/
protected lemma sq_sub_sq (h : Commute a b) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by
  rw [sq, sq, h.mul_self_sub_mul_self_eq]
/-
**Commute.sub_sq** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {a b : R}, Commute a b → (a - b) ^ 2 = a ^ 
2 - 2 * a * b + b ^ 2
参数：a - b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma sub_sq {a b : R} (h : Commute a b) :
    (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by
  simp [sq, add_mul, sub_mul, mul_sub, two_mul, h.eq, ← sub_add, ← sub_sub]

variable [NoZeroDivisors R]
/-
**Commute.sq_eq_sq_iff_eq_or_eq_neg** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {a b : R} [NoZeroDivisors R], Commute a b →
 (a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b)
参数：a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Commute.sq_sub_sq`：∀ {R : Type u} [inst : Ring R] {a b : R}, Commute a b
 → a ^ 2 - b ^ 2 = (a + b) * (a - b)
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `add_eq_zero_iff_eq_neg`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ a = -b
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma sq_eq_sq_iff_eq_or_eq_neg (h : Commute a b) : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b := by
  rw [← sub_eq_zero, h.sq_sub_sq, mul_eq_zero, add_eq_zero_iff_eq_neg, sub_eq_zero, or_comm]

end Ring
end Commute

section HasDistribNeg
variable (R)
variable [Monoid R] [HasDistribNeg R]

/-
**neg_one_pow_eq_or** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (R : Type u) [inst : Monoid R] [inst_1 : HasDistribNeg R] (n : ℕ), (-1) 
^ n = 1 ∨ (-1) ^ n = -1
参数：R : Type u；n : ℕ；-1；-1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma neg_one_pow_eq_or : ∀ n : ℕ, (-1 : R) ^ n = 1 ∨ (-1 : R) ^ n = -1
  | 0 => Or.inl (pow_zero _)
  | n + 1 => (neg_one_pow_eq_or n).symm.imp
    (fun h ↦ by rw [pow_succ, h, neg_one_mul, neg_neg])
    (fun h ↦ by rw [pow_succ, h, one_mul])

variable {R}
/-
**neg_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_pow (a : R) (n : Nat) : (-a) ^ n = (-1) ^ n * a ^ n
参数：a : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.mul_pow`：∀ {M : Type u_2} [inst : Monoid M] {a b : M}, Commute a
 b → ∀ (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `Commute.neg_one_left`：neg_one_left (a : R) : Commute (-1) a
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
-/
lemma neg_pow (a : R) (n : ℕ) : (-a) ^ n = (-1) ^ n * a ^ n :=
  neg_one_mul a ▸ (Commute.neg_one_left a).mul_pow n
/-
**neg_pow'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_pow' (a : R) (n : Nat) : (-a) ^ n = a ^ n * (-1) ^ n
参数：a : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.mul_pow`：∀ {M : Type u_2} [inst : Monoid M] {a b : M}, Commute a
 b → ∀ (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `Commute.neg_one_right`：neg_one_right (a : R) : Commute a (-1)
· 使用定理 `mul_neg_one`：mul_neg_one (a : α) : a * -1 = -a
-/
lemma neg_pow' (a : R) (n : ℕ) : (-a) ^ n = a ^ n * (-1) ^ n :=
  mul_neg_one a ▸ (Commute.neg_one_right a).mul_pow n
/-
**neg_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_sq (a : R) : (-a) ^ 2 = a ^ 2
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma neg_sq (a : R) : (-a) ^ 2 = a ^ 2 := by simp [sq]
/-
**neg_one_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_one_sq : (-1 : R) ^ 2 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `neg_sq`：neg_sq (a : R) : (-a) ^ 2 = a ^ 2
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma neg_one_sq : (-1 : R) ^ 2 = 1 := by simp [neg_sq, one_pow]

alias neg_pow_two := neg_sq

alias neg_one_pow_two := neg_one_sq

end HasDistribNeg

section Ring
variable [Ring R] {a : R} {n : ℕ}

/-
**neg_one_pow_mul_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u} [inst : Ring R] {a : R} {n : ℕ}, (-1) ^ n * a = 0 ↔ a = 0
参数：-1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_one_pow_eq_or`：∀ (R : Type u) [inst : Monoid R] [inst_1 : HasDistrib
Neg R] (n : ℕ), (-1) ^ n = 1 ∨ (-1) ^ n = -1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
-/
@[simp] lemma neg_one_pow_mul_eq_zero_iff : (-1) ^ n * a = 0 ↔ a = 0 := by
  rcases neg_one_pow_eq_or R n with h | h <;> simp [h]
/-
**mul_neg_one_pow_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u} [inst : Ring R] {a : R} {n : ℕ}, a * (-1) ^ n = 0 ↔ a = 0
参数：-1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_one_pow_eq_or`：∀ (R : Type u) [inst : Monoid R] [inst_1 : HasDistrib
Neg R] (n : ℕ), (-1) ^ n = 1 ∨ (-1) ^ n = -1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
-/
@[simp] lemma mul_neg_one_pow_eq_zero_iff : a * (-1) ^ n = 0 ↔ a = 0 := by
  obtain h | h := neg_one_pow_eq_or R n <;> simp [h]
/-
**neg_one_pow_eq_pow_mod_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_one_pow_eq_pow_mod_two (n : Nat) : (-1 : R) ^ n = (-1) ^ (n % 2)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Nat.add_mul_mod_self_left`：∀ (x y z : ℕ), (x + y * z) % y = x % y
· 使用定理 `Nat.mod_mod_of_dvd`：∀ {c b : ℕ} (a : ℕ), c ∣ b → a % b % c = a % c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma neg_one_pow_eq_pow_mod_two (n : ℕ) : (-1 : R) ^ n = (-1) ^ (n % 2) := by
  rw [← Nat.mod_add_div n 2, pow_add, pow_mul]; simp [sq]

variable [NoZeroDivisors R]
/-
**sq_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u} [inst : Ring R] {a : R} [NoZeroDivisors R], a ^ 2 = 1 ↔ a =
 1 ∨ a = -1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Commute.sq_eq_sq_iff_eq_or_eq_neg`：∀ {R : Type u} [inst : Ring R] {a b :
 R} [NoZeroDivisors R], Commute a b → (a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b)
· 使用定理 `Commute.one_right`：one_right (a : M) : Commute a 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma sq_eq_one_iff : a ^ 2 = 1 ↔ a = 1 ∨ a = -1 := by
  rw [← (Commute.one_right a).sq_eq_sq_iff_eq_or_eq_neg, one_pow]
/-
**sq_ne_one_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sq_ne_one_iff : a ^ 2 != 1 ↔ a != 1 ∧ a != -1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `sq_eq_one_iff`：∀ {R : Type u} [inst : Ring R] {a : R} [NoZeroDivisors R]
, a ^ 2 = 1 ↔ a = 1 ∨ a = -1
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
-/
lemma sq_ne_one_iff : a ^ 2 ≠ 1 ↔ a ≠ 1 ∧ a ≠ -1 := sq_eq_one_iff.not.trans not_or

end Ring

/-- Representation of a difference of two squares in a commutative ring as a product. -/
/-
**mul_self_sub_mul_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_self_sub_mul_self [NonUnitalNonAssocCommRing R] (a b : R) : a * a - b 
* b = (a + b) * (a - b)
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.mul_self_sub_mul_self_eq`：mul_self_sub_mul_self_eq [NonUnitalNon
AssocRing R] {a b : R} (h : Commute a b) : a * a - b * b = (a + b) * (a - b)
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b

--- 原说明 ---
Representation of a difference of two squares in a commutative ring as a product
.
-/
theorem mul_self_sub_mul_self [NonUnitalNonAssocCommRing R] (a b : R) :
    a * a - b * b = (a + b) * (a - b) :=
  (Commute.all a b).mul_self_sub_mul_self_eq
/-
**mul_self_sub_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_self_sub_one [NonAssocRing R] (a : R) : a * a - 1 = (a + 1) * (a - 1)
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Commute.mul_self_sub_mul_self_eq`：mul_self_sub_mul_self_eq [NonUnitalNon
AssocRing R] {a b : R} (h : Commute a b) : a * a - b * b = (a + b) * (a - b)
· 使用定理 `Commute.one_right`：one_right (a : M) : Commute a 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mul_self_sub_one [NonAssocRing R] (a : R) : a * a - 1 = (a + 1) * (a - 1) := by
  rw [← (Commute.one_right a).mul_self_sub_mul_self_eq, mul_one]
/-
**mul_self_eq_mul_self_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_self_eq_mul_self_iff [NonUnitalNonAssocCommRing R] [NoZeroDivisors R] 
{a b : R} : a * a = b * b ↔ a = b ∨ a = -b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.mul_self_eq_mul_self_iff`：mul_self_eq_mul_self_iff [NonUnitalNon
AssocRing R] [NoZeroDivisors R] {a b : R} (h : Commute a b) : a * a = b * b ↔ a 
= b ∨ a = -b
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem mul_self_eq_mul_self_iff [NonUnitalNonAssocCommRing R] [NoZeroDivisors R] {a b : R} :
    a * a = b * b ↔ a = b ∨ a = -b :=
  (Commute.all a b).mul_self_eq_mul_self_iff
/-
**mul_self_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_self_eq_one_iff [NonAssocRing R] [NoZeroDivisors R] {a : R} : a * a = 
1 ↔ a = 1 ∨ a = -1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Commute.mul_self_eq_mul_self_iff`：mul_self_eq_mul_self_iff [NonUnitalNon
AssocRing R] [NoZeroDivisors R] {a b : R} (h : Commute a b) : a * a = b * b ↔ a 
= b ∨ a = -b
· 使用定理 `Commute.one_right`：one_right (a : M) : Commute a 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_self_eq_one_iff [NonAssocRing R] [NoZeroDivisors R] {a : R} :
    a * a = 1 ↔ a = 1 ∨ a = -1 := by
  rw [← (Commute.one_right a).mul_self_eq_mul_self_iff, mul_one]

section CommRing
variable [CommRing R]

/-
**sq_sub_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sq_sub_sq (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b)
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.sq_sub_sq`：∀ {R : Type u} [inst : Ring R] {a b : R}, Commute a b
 → a ^ 2 - b ^ 2 = (a + b) * (a - b)
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
lemma sq_sub_sq (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := (Commute.all a b).sq_sub_sq

alias pow_two_sub_pow_two := sq_sub_sq
/-
**sub_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sub_sq (a b : R) : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `add_sq`：add_sq (a b : α) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2
· 使用引理 `neg_sq`：neg_sq (a : R) : (-a) ^ 2 = a ^ 2
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma sub_sq (a b : R) : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by
  rw [sub_eq_add_neg, add_sq, neg_sq, mul_neg, ← sub_eq_add_neg]

alias sub_pow_two := sub_sq
/-
**sub_sq'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sub_sq' (a b : R) : (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `add_sq'`：add_sq' (a b : α) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b
· 使用引理 `neg_sq`：neg_sq (a : R) : (-a) ^ 2 = a ^ 2
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma sub_sq' (a b : R) : (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b := by
  rw [sub_eq_add_neg, add_sq', neg_sq, mul_neg, ← sub_eq_add_neg]
/-
**sub_sq_comm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sub_sq_comm (a b : R) : (a - b) ^ 2 = (b - a) ^ 2
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `sub_sq'`：sub_sq' (a b : R) : (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
lemma sub_sq_comm (a b : R) : (a - b) ^ 2 = (b - a) ^ 2 := by
  rw [sub_sq', mul_right_comm, add_comm, sub_sq']

variable [NoZeroDivisors R] {a b : R}
/-
**sq_eq_sq_iff_eq_or_eq_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sq_eq_sq_iff_eq_or_eq_neg : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.sq_eq_sq_iff_eq_or_eq_neg`：∀ {R : Type u} [inst : Ring R] {a b :
 R} [NoZeroDivisors R], Commute a b → (a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b)
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
lemma sq_eq_sq_iff_eq_or_eq_neg : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b :=
  (Commute.all a b).sq_eq_sq_iff_eq_or_eq_neg
/-
**eq_or_eq_neg_of_sq_eq_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_or_eq_neg_of_sq_eq_sq (a b : R) : a ^ 2 = b ^ 2 -> a = b ∨ a = -b
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `sq_eq_sq_iff_eq_or_eq_neg`：sq_eq_sq_iff_eq_or_eq_neg : a ^ 2 = b ^ 2 ↔ a
 = b ∨ a = -b
-/
lemma eq_or_eq_neg_of_sq_eq_sq (a b : R) : a ^ 2 = b ^ 2 → a = b ∨ a = -b :=
  sq_eq_sq_iff_eq_or_eq_neg.1

-- Copies of the above CommRing lemmas for `Units R`.
namespace Units

/-
**Units.sq_eq_sq_iff_eq_or_eq_neg** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] [NoZeroDivisors R] {a b : Rˣ}, a ^ 2 = 
b ^ 2 ↔ a = b ∨ a = -b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma sq_eq_sq_iff_eq_or_eq_neg {a b : Rˣ} : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b := by
  simp_rw [Units.ext_iff, val_pow_eq_pow_val, sq_eq_sq_iff_eq_or_eq_neg, Units.val_neg]
/-
**Units.eq_or_eq_neg_of_sq_eq_sq** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] [NoZeroDivisors R] (a b : Rˣ), a ^ 2 = 
b ^ 2 → a = b ∨ a = -b
参数：a b : Rˣ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Units.sq_eq_sq_iff_eq_or_eq_neg`：∀ {R : Type u} [inst : CommRing R] [NoZ
eroDivisors R] {a b : Rˣ}, a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b
-/
protected lemma eq_or_eq_neg_of_sq_eq_sq (a b : Rˣ) (h : a ^ 2 = b ^ 2) : a = b ∨ a = -b :=
  Units.sq_eq_sq_iff_eq_or_eq_neg.1 h

end Units
end CommRing

namespace Units

/-- In the unit group of an integral domain, a unit is its own inverse iff the unit is one or
  one's additive inverse. -/
/-
**Units.inv_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：inv_eq_self_iff [Ring R] [NoZeroDivisors R] (u : Rˣ) : u⁻¹ = u ↔ u = 1 ∨ u
 = -1
参数：u : Rˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_eq_iff_mul_eq_one`：inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_self_eq_one_iff`：mul_self_eq_one_iff [NonAssocRing R] [NoZeroDivisor
s R] {a : R} : a * a = 1 ↔ a = 1 ∨ a = -1

--- 原说明 ---
In the unit group of an integral domain, a unit is its own inverse iff the unit 
is one or
  one's additive inverse.
-/
theorem inv_eq_self_iff [Ring R] [NoZeroDivisors R] (u : Rˣ) : u⁻¹ = u ↔ u = 1 ∨ u = -1 := by
  rw [inv_eq_iff_mul_eq_one]
  simp only [Units.ext_iff]
  push_cast
  exact mul_self_eq_one_iff

end Units

section Bracket

variable [NonUnitalNonAssocRing R]

namespace Ring

/-
**Ring.** 是 Mathlib 中的一个实例，位于命名空间 `Ring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) instBracket : Bracket R R := ⟨fun x y => x * y - y * x⟩
/-
**Ring.lie_def** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：lie_def (x y : R) : ⁅x, y⁆ = x * y - y * x
参数：x y : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lie_def (x y : R) : ⁅x, y⁆ = x * y - y * x := rfl

end Ring

/-
**commute_iff_lie_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commute_iff_lie_eq {x y : R} : Commute x y ↔ ⁅x, y⁆ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
-/
theorem commute_iff_lie_eq {x y : R} : Commute x y ↔ ⁅x, y⁆ = 0 := sub_eq_zero.symm
/-
**Commute.lie_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Commute.lie_eq {x y : R} (h : Commute x y) : ⁅x, y⁆ = 0
参数：h : Commute x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_eq_zero_of_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a = b
 → a - b = 0
-/
theorem Commute.lie_eq {x y : R} (h : Commute x y) : ⁅x, y⁆ = 0 := sub_eq_zero_of_eq h

end Bracket

