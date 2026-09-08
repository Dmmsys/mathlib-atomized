/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Michael Stoll
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Legendre symbol

This file contains results about Legendre symbols.

We define the Legendre symbol $\Bigl(\frac{a}{p}\Bigr)$ as `legendreSym p a`.
Note the order of arguments! The advantage of this form is that then `legendreSym p`
is a multiplicative map.

The Legendre symbol is used to define the Jacobi symbol, `jacobiSym a b`, for integers `a`
and (odd) natural numbers `b`, which extends the Legendre symbol.

## Main results

We also prove the supplementary laws that give conditions for when `-1`
is a square modulo a prime `p`:
`legendreSym.at_neg_one` and `ZMod.exists_sq_eq_neg_one_iff` for `-1`.

See `NumberTheory.LegendreSymbol.QuadraticReciprocity` for the conditions when `2` and `-2`
are squares:
`legendreSym.at_two` and `ZMod.exists_sq_eq_two_iff` for `2`,
`legendreSym.at_neg_two` and `ZMod.exists_sq_eq_neg_two_iff` for `-2`.

## Tags

quadratic residue, quadratic nonresidue, Legendre symbol
-/

@[expose] public section


open Nat

section Euler

namespace ZMod

variable (p : ℕ) [Fact p.Prime]

/-- Euler's Criterion: A unit `x` of `ZMod p` is a square if and only if `x ^ (p / 2) = 1`. -/
/-
**ZMod.euler_criterion_units** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：euler_criterion_units (x : (ZMod p)ˣ) : (exists y : (ZMod p)ˣ, y ^ 2 = x) 
↔ x ^ (p / 2) = 1
参数：x : (ZMod p)ˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `FiniteField.unit_isSquare_iff`：unit_isSquare_iff (hF : ringChar F != 2) 
(a : Fˣ) : IsSquare a ↔ a ^ (Fintype.card F / 2) = 1
· 使用定理 `ZMod.ringChar_zmod_n`：ringChar_zmod_n (n : Nat) : ringChar (ZMod n) = n
· 使用引理 `isSquare_iff_exists_sq`：isSquare_iff_exists_sq (a : α) : IsSquare a ↔ ex
ists r, a = r ^ 2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n

--- 原说明 ---
Euler's Criterion: A unit `x` of `ZMod p` is a square if and only if `x ^ (p / 2
) = 1`.
-/
theorem euler_criterion_units (x : (ZMod p)ˣ) : (∃ y : (ZMod p)ˣ, y ^ 2 = x) ↔ x ^ (p / 2) = 1 := by
  by_cases hc : p = 2
  · subst hc
    simp only [eq_iff_true_of_subsingleton, exists_const]
  · have h₀ := FiniteField.unit_isSquare_iff (by rwa [ringChar_zmod_n]) x
    have hs : (∃ y : (ZMod p)ˣ, y ^ 2 = x) ↔ IsSquare x := by
      rw [isSquare_iff_exists_sq x]
      simp_rw [eq_comm]
    rw [hs]
    rwa [card p] at h₀

/-- Euler's Criterion: a nonzero `a : ZMod p` is a square if and only if `x ^ (p / 2) = 1`. -/
/-
**ZMod.euler_criterion** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：euler_criterion {a : ZMod p} (ha : a != 0) : IsSquare (a : ZMod p) ↔ a ^ (
p / 2) = 1
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `iff_congr`：∀ {p₁ p₂ q₁ q₂ : Prop}, (p₁ ↔ p₂) → (q₁ ↔ q₂) → ((p₁ ↔ q₁) ↔ 
(p₂ ↔ q₂))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `ZMod.euler_criterion_units`：euler_criterion_units (x : (ZMod p)ˣ) : (exi
sts y : (ZMod p)ˣ, y ^ 2 = x) ↔ x ^ (p / 2) = 1

--- 原说明 ---
Euler's Criterion: a nonzero `a : ZMod p` is a square if and only if `x ^ (p / 2
) = 1`.
-/
theorem euler_criterion {a : ZMod p} (ha : a ≠ 0) : IsSquare (a : ZMod p) ↔ a ^ (p / 2) = 1 := by
  apply (iff_congr _ (by simp [Units.ext_iff])).mp (euler_criterion_units p (Units.mk0 a ha))
  simp only [Units.ext_iff, sq, Units.val_mk0, Units.val_mul]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, hy.symm⟩
  · rintro ⟨y, rfl⟩
    have hy : y ≠ 0 := by
      rintro rfl
      simp [mul_zero, ne_eq] at ha
    refine ⟨Units.mk0 y hy, ?_⟩; simp

set_option backward.isDefEq.respectTransparency false in
/-- If `a : ZMod p` is nonzero, then `a^(p/2)` is either `1` or `-1`. -/
/-
**ZMod.pow_div_two_eq_neg_one_or_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：pow_div_two_eq_neg_one_or_one {a : ZMod p} (ha : a != 0) : a ^ (p / 2) = 1
 ∨ a ^ (p / 2) = -1
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.eq_two_or_odd`：∀ {p : ℕ}, Nat.Prime p → p = 2 ∨ p % 2 = 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.div_self`：∀ {n : ℕ}, 0 < n → n / n = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ZMod.neg_eq_self_mod_two`：neg_eq_self_mod_two (a : ZMod 2) : -a = a
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_self_eq_one_iff`：mul_self_eq_one_iff [NonAssocRing R] [NoZeroDivisor
s R] {a : R} : a * a = 1 ↔ a = 1 ∨ a = -1
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `ZMod.instIsDomain`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], IsDomain (ZMod p
)
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
If `a : ZMod p` is nonzero, then `a^(p/2)` is either `1` or `-1`.
-/
theorem pow_div_two_eq_neg_one_or_one {a : ZMod p} (ha : a ≠ 0) :
    a ^ (p / 2) = 1 ∨ a ^ (p / 2) = -1 := by
  rcases Prime.eq_two_or_odd (@Fact.out p.Prime _) with rfl | hp_odd
  · revert a ha; intro a; fin_cases a
    · tauto
    · simp
  rw [← mul_self_eq_one_iff, ← pow_add, ← two_mul, two_mul_odd_div_two hp_odd]
  exact pow_card_sub_one_eq_one ha

end ZMod

end Euler

section Legendre

/-!
### Definition of the Legendre symbol and basic properties
-/


open ZMod

variable (p : ℕ) [Fact p.Prime]

/-- The Legendre symbol of `a : ℤ` and a prime `p`, `legendreSym p a`,
is an integer defined as

* `0` if `a` is `0` modulo `p`;
* `1` if `a` is a nonzero square modulo `p`
* `-1` otherwise.

Note the order of the arguments! The advantage of the order chosen here is
that `legendreSym p` is a multiplicative function `ℤ → ℤ`.
-/
/-
**legendreSym** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：legendreSym (a : Int) : Int
参数：a : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Legendre symbol of `a : ℤ` and a prime `p`, `legendreSym p a`,
is an integer defined as

* `0` if `a` is `0` modulo `p`;
* `1` if `a` is a nonzero square modulo `p`
* `-1` otherwise.

Note the order of the arguments! The advantage of the order chosen here is
that `legendreSym p` is a multiplicative function `ℤ → ℤ`.
-/
def legendreSym (a : ℤ) : ℤ :=
  quadraticChar (ZMod p) a

namespace legendreSym

set_option backward.isDefEq.respectTransparency false in
/-- We have the congruence `legendreSym p a ≡ a ^ (p / 2) mod p`. -/
/-
**legendreSym.eq_pow** 是 Mathlib 中的一个定理，位于命名空间 `legendreSym`。
形式化陈述：eq_pow (a : Int) : (legendreSym p a : ZMod p) = (a : ZMod p) ^ (p / 2)
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `legendreSym.eq_1`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (a : ℤ), legendr
eSym p a = (quadraticChar (ZMod p)) ↑a
· 使用定理 `quadraticChar_zero`：quadraticChar_zero : quadraticChar F 0 = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.div_pos`：∀ {b a : ℕ}, b ≤ a → 0 < b → 0 < a / b
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `ZMod.ringChar_zmod_n`：ringChar_zmod_n (n : Nat) : ringChar (ZMod n) = n
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `quadraticChar_eq_one_of_char_two`：quadraticChar_eq_one_of_char_two (hF :
 ringChar F = 2) {a : F} (ha : a != 0) : quadraticChar F a = 1
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
We have the congruence `legendreSym p a ≡ a ^ (p / 2) mod p`.
-/
theorem eq_pow (a : ℤ) : (legendreSym p a : ZMod p) = (a : ZMod p) ^ (p / 2) := by
  rcases eq_or_ne (ringChar (ZMod p)) 2 with hc | hc
  · by_cases ha : (a : ZMod p) = 0
    · rw [legendreSym, ha, quadraticChar_zero,
        zero_pow (Nat.div_pos (@Fact.out p.Prime).two_le (succ_pos 1)).ne']
      norm_cast
    · have := (ringChar_zmod_n p).symm.trans hc
      -- p = 2
      subst p
      rw [legendreSym, quadraticChar_eq_one_of_char_two hc ha]
      revert ha
      push_cast
      generalize (a : ZMod 2) = b; fin_cases b
      · tauto
      · simp
  · convert! quadraticChar_eq_pow_of_char_ne_two' hc (a : ZMod p)
    exact (card p).symm

/-- If `p ∤ a`, then `legendreSym p a` is `1` or `-1`. -/
/-
**legendreSym.eq_one_or_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `legendreSym`。
形式化陈述：eq_one_or_neg_one {a : Int} (ha : (a : ZMod p) != 0) : legendreSym p a = 1
 ∨ legendreSym p a = -1
参数：ha : (a : ZMod p) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `quadraticChar_dichotomy`：quadraticChar_dichotomy {a : F} (ha : a != 0) :
 quadraticChar F a = 1 ∨ quadraticChar F a = -1

--- 原说明 ---
If `p ∤ a`, then `legendreSym p a` is `1` or `-1`.
-/
theorem eq_one_or_neg_one {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    legendreSym p a = 1 ∨ legendreSym p a = -1 :=
  quadraticChar_dichotomy ha
/-
**legendreSym.eq_neg_one_iff_not_one** 是 Mathlib 中的一个定理，位于命名空间 `legendreSym`。
形式化陈述：eq_neg_one_iff_not_one {a : Int} (ha : (a : ZMod p) != 0) : legendreSym p 
a = -1 ↔ ¬legendreSym p a = 1
参数：ha : (a : ZMod p) != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `quadraticChar_eq_neg_one_iff_not_one`：quadraticChar_eq_neg_one_iff_not_o
ne {a : F} (ha : a != 0) : quadraticChar F a = -1 ↔ ¬quadraticChar F a = 1
-/
theorem eq_neg_one_iff_not_one {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    legendreSym p a = -1 ↔ ¬legendreSym p a = 1 :=
  quadraticChar_eq_neg_one_iff_not_one ha

/-- The Legendre symbol of `p` and `a` is zero iff `p ∣ a`. -/
/-
**legendreSym.eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `legendreSym`。
形式化陈述：eq_zero_iff (a : Int) : legendreSym p a = 0 ↔ (a : ZMod p) = 0
参数：a : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `quadraticChar_eq_zero_iff`：quadraticChar_eq_zero_iff {a : F} : quadratic
Char F a = 0 ↔ a = 0

--- 原说明 ---
The Legendre symbol of `p` and `a` is zero iff `p ∣ a`.
-/
theorem eq_zero_iff (a : ℤ) : legendreSym p a = 0 ↔ (a : ZMod p) = 0 :=
  quadraticChar_eq_zero_iff

@[simp]
/-
**legendreSym.at_zero** 是 Mathlib 中的一个定理，位于命名空间 `legendreSym`。
形式化陈述：at_zero : legendreSym p 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `legendreSym.eq_1`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (a : ℤ), legendr
eSym p a = (quadraticChar (ZMod p)) ↑a
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `MulChar.map_zero`：∀ {R' : Type u_2} [inst : CommMonoidWithZero R'] {R : 
Type u_3} [inst_1 : CommMonoidWithZero R] [Nontrivial R]   (χ : MulChar R R'), χ
 0 = 0
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
-/
theorem at_zero : legendreSym p 0 = 0 := by rw [legendreSym, Int.cast_zero, MulChar.map_zero]

@[simp]
/-
**legendreSym.at_one** 是 Mathlib 中的一个定理，位于命名空间 `legendreSym`。
形式化陈述：at_one : legendreSym p 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `legendreSym.eq_1`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (a : ℤ), legendr
eSym p a = (quadraticChar (ZMod p)) ↑a
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `MulChar.map_one`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : Type u_2} 
[inst_1 : CommMonoidWithZero R'] (χ : MulChar R R'), χ 1 = 1
-/
theorem at_one : legendreSym p 1 = 1 := by rw [legendreSym, Int.cast_one, MulChar.map_one]

/-- The Legendre symbol is multiplicative in `a` for `p` fixed. -/
/-
**legendreSym.mul** 是 Mathlib 中的一个定理，位于命名空间 `legendreSym`。
形式化陈述：∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (a b : ℤ), legendreSym p (a * b) = l
egendreSym p a * legendreSym p b
参数：p : ℕ；Nat.Prime p；a b : ℤ；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `quadraticChar_apply`：∀ (F : Type u_1) [inst : Field F] [inst_1 : Fintype
 F] [inst_2 : DecidableEq F] (a : F),   (quadraticChar F) a = quadraticCharFun F
 a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Legendre symbol is multiplicative in `a` for `p` fixed.
-/
protected theorem mul (a b : ℤ) : legendreSym p (a * b) = legendreSym p a * legendreSym p b := by
  simp [legendreSym, Int.cast_mul, map_mul]

/-- The Legendre symbol is a homomorphism of monoids with zero. -/
@[simps]
/-
**legendreSym.hom** 是 Mathlib 中的一个定义，位于命名空间 `legendreSym`。
形式化陈述：hom : Int ->*₀ Int where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `legendreSym.at_zero`：at_zero : legendreSym p 0 = 0
· 使用定理 `legendreSym.at_one`：at_one : legendreSym p 1 = 1
· 使用定理 `legendreSym.mul`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (a b : ℤ), legend
reSym p (a * b) = legendreSym p a * legendreSym p b

--- 原说明 ---
The Legendre symbol is a homomorphism of monoids with zero.
-/
def hom : ℤ →*₀ ℤ where
  toFun := legendreSym p
  map_zero' := at_zero p
  map_one' := at_one p
  map_mul' := legendreSym.mul p

/-- The square of the symbol is 1 if `p ∤ a`. -/
/-
**legendreSym.sq_one** 是 Mathlib 中的一个定理，位于命名空间 `legendreSym`。
形式化陈述：sq_one {a : Int} (ha : (a : ZMod p) != 0) : legendreSym p a ^ 2 = 1
参数：ha : (a : ZMod p) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `quadraticChar_sq_one`：quadraticChar_sq_one {a : F} (ha : a != 0) : quadr
aticChar F a ^ 2 = 1

--- 原说明 ---
The square of the symbol is 1 if `p ∤ a`.
-/
theorem sq_one {a : ℤ} (ha : (a : ZMod p) ≠ 0) : legendreSym p a ^ 2 = 1 :=
  quadraticChar_sq_one ha

/-- The Legendre symbol of `a^2` at `p` is 1 if `p ∤ a`. -/
/-
**legendreSym.sq_one'** 是 Mathlib 中的一个定理，位于命名空间 `legendreSym`。
形式化陈述：sq_one' {a : Int} (ha : (a : ZMod p) != 0) : legendreSym p (a ^ 2) = 1
参数：ha : (a : ZMod p) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `quadraticChar_sq_one'`：quadraticChar_sq_one' {a : F} (ha : a != 0) : qua
draticChar F (a ^ 2) = 1

--- 原说明 ---
The Legendre symbol of `a^2` at `p` is 1 if `p ∤ a`.
-/
theorem sq_one' {a : ℤ} (ha : (a : ZMod p) ≠ 0) : legendreSym p (a ^ 2) = 1 := by
  dsimp only [legendreSym]
  rw [Int.cast_pow]
  exact quadraticChar_sq_one' ha

/-- The Legendre symbol depends only on `a` mod `p`. -/
/-
**legendreSym.mod** 是 Mathlib 中的一个定理，位于命名空间 `legendreSym`。
形式化陈述：∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (a : ℤ), legendreSym p a = legendreS
ym p (a % ↑p)
参数：p : ℕ；Nat.Prime p；a : ℤ；a % ↑p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.intCast_mod`：intCast_mod (a : Int) (b : Nat) : ((a % b : Int) : ZMo
d b) = (a : ZMod b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Legendre symbol depends only on `a` mod `p`.
-/
protected theorem mod (a : ℤ) : legendreSym p a = legendreSym p (a % p) := by
  simp only [legendreSym, intCast_mod]

/-- When `p ∤ a`, then `legendreSym p a = 1` iff `a` is a square mod `p`. -/
/-
**legendreSym.eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `legendreSym`。
形式化陈述：eq_one_iff {a : Int} (ha0 : (a : ZMod p) != 0) : legendreSym p a = 1 ↔ IsS
quare (a : ZMod p)
参数：ha0 : (a : ZMod p) != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `quadraticChar_one_iff_isSquare`：quadraticChar_one_iff_isSquare {a : F} (
ha : a != 0) : quadraticChar F a = 1 ↔ IsSquare a

--- 原说明 ---
When `p ∤ a`, then `legendreSym p a = 1` iff `a` is a square mod `p`.
-/
theorem eq_one_iff {a : ℤ} (ha0 : (a : ZMod p) ≠ 0) : legendreSym p a = 1 ↔ IsSquare (a : ZMod p) :=
  quadraticChar_one_iff_isSquare ha0
/-
**legendreSym.eq_one_iff'** 是 Mathlib 中的一个定理，位于命名空间 `legendreSym`。
形式化陈述：eq_one_iff' {a : Nat} (ha0 : (a : ZMod p) != 0) : legendreSym p a = 1 ↔ Is
Square (a : ZMod p)
参数：ha0 : (a : ZMod p) != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `legendreSym.eq_one_iff`：eq_one_iff {a : Int} (ha0 : (a : ZMod p) != 0) :
 legendreSym p a = 1 ↔ IsSquare (a : ZMod p)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_one_iff' {a : ℕ} (ha0 : (a : ZMod p) ≠ 0) :
    legendreSym p a = 1 ↔ IsSquare (a : ZMod p) := by
  rw [eq_one_iff]
  · norm_cast
  · exact mod_cast ha0

/-- `legendreSym p a = -1` iff `a` is a nonsquare mod `p`. -/
/-
**legendreSym.eq_neg_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `legendreSym`。
形式化陈述：eq_neg_one_iff {a : Int} : legendreSym p a = -1 ↔ ¬IsSquare (a : ZMod p)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `quadraticChar_neg_one_iff_not_isSquare`：quadraticChar_neg_one_iff_not_is
Square {a : F} : quadraticChar F a = -1 ↔ ¬IsSquare a

--- 原说明 ---
`legendreSym p a = -1` iff `a` is a nonsquare mod `p`.
-/
theorem eq_neg_one_iff {a : ℤ} : legendreSym p a = -1 ↔ ¬IsSquare (a : ZMod p) :=
  quadraticChar_neg_one_iff_not_isSquare
/-
**legendreSym.eq_neg_one_iff'** 是 Mathlib 中的一个定理，位于命名空间 `legendreSym`。
形式化陈述：eq_neg_one_iff' {a : Nat} : legendreSym p a = -1 ↔ ¬IsSquare (a : ZMod p)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `legendreSym.eq_neg_one_iff`：eq_neg_one_iff {a : Int} : legendreSym p a =
 -1 ↔ ¬IsSquare (a : ZMod p)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_neg_one_iff' {a : ℕ} : legendreSym p a = -1 ↔ ¬IsSquare (a : ZMod p) := by
  rw [eq_neg_one_iff]; norm_cast

/-- The number of square roots of `a` modulo `p` is determined by the Legendre symbol. -/
/-
**legendreSym.card_sqrts** 是 Mathlib 中的一个定理，位于命名空间 `legendreSym`。
形式化陈述：card_sqrts (hp : p != 2) (a : Int) : ↑{x : ZMod p | x ^ 2 = a}.toFinset.ca
rd = legendreSym p a + 1
参数：hp : p != 2；a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `quadraticChar_card_sqrts`：quadraticChar_card_sqrts (hF : ringChar F != 2
) (a : F) : #{x : F | x ^ 2 = a}.toFinset = quadraticChar F a + 1
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `ZMod.ringChar_zmod_n`：ringChar_zmod_n (n : Nat) : ringChar (ZMod n) = n

--- 原说明 ---
The number of square roots of `a` modulo `p` is determined by the Legendre symbo
l.
-/
theorem card_sqrts (hp : p ≠ 2) (a : ℤ) :
    ↑{x : ZMod p | x ^ 2 = a}.toFinset.card = legendreSym p a + 1 :=
  quadraticChar_card_sqrts ((ringChar_zmod_n p).substr hp) a

end legendreSym

end Legendre

section QuadraticForm

/-!
### Applications to binary quadratic forms
-/


namespace legendreSym

/-- The Legendre symbol `legendreSym p a = 1` if there is a solution in `ℤ/pℤ`
of the equation `x^2 - a*y^2 = 0` with `y ≠ 0`. -/
/-
**legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `legendr
eSym`。
形式化陈述：eq_one_of_sq_sub_mul_sq_eq_zero {p : Nat} [Fact p.Prime] {a : Int} (ha : (
a : ZMod p) != 0) {x y : ZMod p} (hy : y != 0) (hxy : x ^ 2 - a * y ^ 2 = 0) : l
egendreSym p a = 1
参数：ha : (a : ZMod p) != 0；hy : y != 0；hxy : x ^ 2 - a * y ^ 2 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `legendreSym.eq_one_iff`：eq_one_iff {a : Int} (ha0 : (a : ZMod p) != 0) :
 legendreSym p a = 1 ↔ IsSquare (a : ZMod p)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
The Legendre symbol `legendreSym p a = 1` if there is a solution in `ℤ/pℤ`
of the equation `x^2 - a*y^2 = 0` with `y ≠ 0`.
-/
theorem eq_one_of_sq_sub_mul_sq_eq_zero {p : ℕ} [Fact p.Prime] {a : ℤ} (ha : (a : ZMod p) ≠ 0)
    {x y : ZMod p} (hy : y ≠ 0) (hxy : x ^ 2 - a * y ^ 2 = 0) : legendreSym p a = 1 := by
  apply_fun (· * y⁻¹ ^ 2) at hxy
  simp only [zero_mul] at hxy
  rw [(by ring : (x ^ 2 - ↑a * y ^ 2) * y⁻¹ ^ 2 = (x * y⁻¹) ^ 2 - a * (y * y⁻¹) ^ 2),
    mul_inv_cancel₀ hy, one_pow, mul_one, sub_eq_zero, pow_two] at hxy
  exact (eq_one_iff p ha).mpr ⟨x * y⁻¹, hxy.symm⟩

/-- The Legendre symbol `legendreSym p a = 1` if there is a solution in `ℤ/pℤ`
of the equation `x^2 - a*y^2 = 0` with `x ≠ 0`. -/
/-
**legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `legend
reSym`。
形式化陈述：eq_one_of_sq_sub_mul_sq_eq_zero' {p : Nat} [Fact p.Prime] {a : Int} (ha : 
(a : ZMod p) != 0) {x y : ZMod p} (hx : x != 0) (hxy : x ^ 2 - a * y ^ 2 = 0) : 
legendreSym p a = 1
参数：ha : (a : ZMod p) != 0；hx : x != 0；hxy : x ^ 2 - a * y ^ 2 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `sq_eq_zero_iff`：sq_eq_zero_iff : a ^ 2 = 0 ↔ a = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `ZMod.instIsDomain`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], IsDomain (ZMod p
)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero`：eq_one_of_sq_sub_mul_sq_eq_
zero {p : Nat} [Fact p.Prime] {a : Int} (ha : (a : ZMod p) != 0) {x y : ZMod p} 
(hy : y != 0) (hxy : x ^ 2 - a * …

--- 原说明 ---
The Legendre symbol `legendreSym p a = 1` if there is a solution in `ℤ/pℤ`
of the equation `x^2 - a*y^2 = 0` with `x ≠ 0`.
-/
theorem eq_one_of_sq_sub_mul_sq_eq_zero' {p : ℕ} [Fact p.Prime] {a : ℤ} (ha : (a : ZMod p) ≠ 0)
    {x y : ZMod p} (hx : x ≠ 0) (hxy : x ^ 2 - a * y ^ 2 = 0) : legendreSym p a = 1 := by
  have hy : y ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, mul_zero, sub_zero, sq_eq_zero_iff] at hxy
    exact hx hxy
  exact eq_one_of_sq_sub_mul_sq_eq_zero ha hy hxy

/-- If `legendreSym p a = -1`, then the only solution of `x^2 - a*y^2 = 0` in `ℤ/pℤ`
is the trivial one. -/
/-
**legendreSym.eq_zero_mod_of_eq_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `legendreSym`。
形式化陈述：eq_zero_mod_of_eq_neg_one {p : Nat} [Fact p.Prime] {a : Int} (h : legendre
Sym p a = -1) {x y : ZMod p} (hxy : x ^ 2 - a * y ^ 2 = 0) : x = 0 ∧ y = 0
参数：h : legendreSym p a = -1；hxy : x ^ 2 - a * y ^ 2 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `legendreSym.eq_zero_iff`：eq_zero_iff (a : Int) : legendreSym p a = 0 ↔ (
a : ZMod p) = 0
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `imp_iff_or_not`：imp_iff_or_not {b a : Prop} : b -> a ↔ a ∨ ¬b
· 使用定理 `not_and'`：∀ {a b : Prop}, ¬(a ∧ b) ↔ b → ¬a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `CharZero.eq_neg_self_iff`：∀ {R : Type u_2} [inst : NonAssocRing R] [NoZe
roDivisors R] [CharZero R] {a : R}, a = -a ↔ a = 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero'`：eq_one_of_sq_sub_mul_sq_eq
_zero' {p : Nat} [Fact p.Prime] {a : Int} (ha : (a : ZMod p) != 0) {x y : ZMod p
} (hx : x != 0) (hxy : x ^ 2 - a *…
· 使用定理 `legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero`：eq_one_of_sq_sub_mul_sq_eq_
zero {p : Nat} [Fact p.Prime] {a : Int} (ha : (a : ZMod p) != 0) {x y : ZMod p} 
(hy : y != 0) (hxy : x ^ 2 - a * …

--- 原说明 ---
If `legendreSym p a = -1`, then the only solution of `x^2 - a*y^2 = 0` in `ℤ/pℤ`
is the trivial one.
-/
theorem eq_zero_mod_of_eq_neg_one {p : ℕ} [Fact p.Prime] {a : ℤ} (h : legendreSym p a = -1)
    {x y : ZMod p} (hxy : x ^ 2 - a * y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  have ha : (a : ZMod p) ≠ 0 := by
    intro hf
    rw [(eq_zero_iff p a).mpr hf] at h
    simp at h
  by_contra hf
  rcases imp_iff_or_not.mp (not_and'.mp hf) with hx | hy
  · rw [eq_one_of_sq_sub_mul_sq_eq_zero' ha hx hxy, CharZero.eq_neg_self_iff] at h
    exact one_ne_zero h
  · rw [eq_one_of_sq_sub_mul_sq_eq_zero ha hy hxy, CharZero.eq_neg_self_iff] at h
    exact one_ne_zero h

/-- If `legendreSym p a = -1` and `p` divides `x^2 - a*y^2`, then `p` must divide `x` and `y`. -/
/-
**legendreSym.prime_dvd_of_eq_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `legendreSym`。
形式化陈述：prime_dvd_of_eq_neg_one {p : Nat} [Fact p.Prime] {a : Int} (h : legendreSy
m p a = -1) {x y : Int} (hxy : (p : Int) ∣ x ^ 2 - a * y ^ 2) : ↑p ∣ x ∧ ↑p ∣ y
参数：h : legendreSym p a = -1；hxy : (p : Int) ∣ x ^ 2 - a * y ^ 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `legendreSym.eq_zero_mod_of_eq_neg_one`：eq_zero_mod_of_eq_neg_one {p : Na
t} [Fact p.Prime] {a : Int} (h : legendreSym p a = -1) {x y : ZMod p} (hxy : x ^
 2 - a * y ^ 2 = 0) : x = 0…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n

--- 原说明 ---
If `legendreSym p a = -1` and `p` divides `x^2 - a*y^2`, then `p` must divide `x
` and `y`.
-/
theorem prime_dvd_of_eq_neg_one {p : ℕ} [Fact p.Prime] {a : ℤ} (h : legendreSym p a = -1) {x y : ℤ}
    (hxy : (p : ℤ) ∣ x ^ 2 - a * y ^ 2) : ↑p ∣ x ∧ ↑p ∣ y := by
  simp_rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hxy ⊢
  push_cast at hxy
  exact eq_zero_mod_of_eq_neg_one h hxy

end legendreSym

end QuadraticForm

section Values

/-!
### The value of the Legendre symbol at `-1`

See `jacobiSym.at_neg_one` for the corresponding statement for the Jacobi symbol.
-/


variable {p : ℕ} [Fact p.Prime]

open ZMod

/-- `legendreSym p (-1)` is given by `χ₄ p`. -/
/-
**legendreSym.at_neg_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：legendreSym.at_neg_one (hp : p != 2) : legendreSym p (-1) = χ₄ p
参数：hp : p != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `quadraticChar_neg_one`：quadraticChar_neg_one [DecidableEq F] (hF : ringC
har F != 2) : quadraticChar F (-1) = χ₄ (Fintype.card F)
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `ZMod.ringChar_zmod_n`：ringChar_zmod_n (n : Nat) : ringChar (ZMod n) = n
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`legendreSym p (-1)` is given by `χ₄ p`.
-/
theorem legendreSym.at_neg_one (hp : p ≠ 2) : legendreSym p (-1) = χ₄ p := by
  simp only [legendreSym, card p, quadraticChar_neg_one ((ringChar_zmod_n p).substr hp),
    Int.cast_neg, Int.cast_one]

/-- The value of the Legendre symbol at `-a` is `χ₄ p` times the value at `a`. -/
/-
**legendreSym.at_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：legendreSym.at_neg (hp : p != 2) (a : Int) : legendreSym p (-a) = χ₄ p * l
egendreSym p a
参数：hp : p != 2；a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_eq_neg_one_mul`：neg_eq_neg_one_mul (a : α) : -a = -1 * a
· 使用定理 `legendreSym.mul`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (a b : ℤ), legend
reSym p (a * b) = legendreSym p a * legendreSym p b
· 使用定理 `legendreSym.at_neg_one`：legendreSym.at_neg_one (hp : p != 2) : legendreS
ym p (-1) = χ₄ p

--- 原说明 ---
The value of the Legendre symbol at `-a` is `χ₄ p` times the value at `a`.
-/
theorem legendreSym.at_neg (hp : p ≠ 2) (a : ℤ) : legendreSym p (-a) = χ₄ p * legendreSym p a := by
  rw [neg_eq_neg_one_mul, legendreSym.mul p (-1) a, legendreSym.at_neg_one hp]

namespace ZMod

/-- `-1` is a square in `ZMod p` iff `p` is not congruent to `3` mod `4`. -/
/-
**ZMod.exists_sq_eq_neg_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：exists_sq_eq_neg_one_iff : IsSquare (-1 : ZMod p) ↔ p % 4 != 3
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteField.isSquare_neg_one_iff`：FiniteField.isSquare_neg_one_iff : IsS
quare (-1 : F) ↔ Fintype.card F % 4 != 3
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`-1` is a square in `ZMod p` iff `p` is not congruent to `3` mod `4`.
-/
theorem exists_sq_eq_neg_one_iff : IsSquare (-1 : ZMod p) ↔ p % 4 ≠ 3 := by
  rw [FiniteField.isSquare_neg_one_iff, card p]
/-
**ZMod.mod_four_ne_three_of_sq_eq_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：mod_four_ne_three_of_sq_eq_neg_one {y : ZMod p} (hy : y ^ 2 = -1) : p % 4 
!= 3
参数：hy : y ^ 2 = -1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ZMod.exists_sq_eq_neg_one_iff`：exists_sq_eq_neg_one_iff : IsSquare (-1 :
 ZMod p) ↔ p % 4 != 3
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
-/
theorem mod_four_ne_three_of_sq_eq_neg_one {y : ZMod p} (hy : y ^ 2 = -1) : p % 4 ≠ 3 :=
  exists_sq_eq_neg_one_iff.1 ⟨y, hy ▸ pow_two y⟩

/-- If two nonzero squares are negatives of each other in `ZMod p`, then `p % 4 ≠ 3`. -/
/-
**ZMod.mod_four_ne_three_of_sq_eq_neg_sq'** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：mod_four_ne_three_of_sq_eq_neg_sq' {x y : ZMod p} (hy : y != 0) (hxy : x ^
 2 = -y ^ 2) : p % 4 != 3
参数：hy : y != 0；hxy : x ^ 2 = -y ^ 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.mod_four_ne_three_of_sq_eq_neg_one`：mod_four_ne_three_of_sq_eq_neg_
one {y : ZMod p} (hy : y ^ 2 = -1) : p % 4 != 3
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
If two nonzero squares are negatives of each other in `ZMod p`, then `p % 4 ≠ 3`
.
-/
theorem mod_four_ne_three_of_sq_eq_neg_sq' {x y : ZMod p} (hy : y ≠ 0) (hxy : x ^ 2 = -y ^ 2) :
    p % 4 ≠ 3 :=
  @mod_four_ne_three_of_sq_eq_neg_one p _ (x / y)
    (by
      apply_fun fun z => z / y ^ 2 at hxy
      rwa [neg_div, ← div_pow, ← div_pow, div_self hy, one_pow] at hxy)
/-
**ZMod.mod_four_ne_three_of_sq_eq_neg_sq** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：mod_four_ne_three_of_sq_eq_neg_sq {x y : ZMod p} (hx : x != 0) (hxy : x ^ 
2 = -y ^ 2) : p % 4 != 3
参数：hx : x != 0；hxy : x ^ 2 = -y ^ 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.mod_four_ne_three_of_sq_eq_neg_sq'`：mod_four_ne_three_of_sq_eq_neg_
sq' {x y : ZMod p} (hy : y != 0) (hxy : x ^ 2 = -y ^ 2) : p % 4 != 3
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
-/
theorem mod_four_ne_three_of_sq_eq_neg_sq {x y : ZMod p} (hx : x ≠ 0) (hxy : x ^ 2 = -y ^ 2) :
    p % 4 ≠ 3 :=
  mod_four_ne_three_of_sq_eq_neg_sq' hx (neg_eq_iff_eq_neg.mpr hxy).symm

end ZMod

end Values

