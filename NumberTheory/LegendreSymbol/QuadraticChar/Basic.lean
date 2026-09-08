/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Fintype.Parity
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Quadratic characters of finite fields

This file defines the quadratic character on a finite field `F` and proves
some basic statements about it.

## Tags

quadratic character
-/

@[expose] public section


/-!
### Definition of the quadratic character

We define the quadratic character of a finite field `F` with values in ℤ.
-/


section Define

/-- Define the quadratic character with values in ℤ on a monoid with zero `α`.
It takes the value zero at zero; for non-zero argument `a : α`, it is `1`
if `a` is a square, otherwise it is `-1`.

This only deserves the name "character" when it is multiplicative,
e.g., when `α` is a finite field. See `quadraticCharFun_mul`.

We will later define `quadraticChar` to be a multiplicative character
of type `MulChar F ℤ`, when the domain is a finite field `F`.
-/
/-
**quadraticCharFun** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：quadraticCharFun (α : Type*) [MonoidWithZero α] [DecidableEq α] [Decidable
Pred (IsSquare : α -> Prop)] (a : α) : Int
参数：α : Type*；IsSquare : α -> Prop；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define the quadratic character with values in ℤ on a monoid with zero `α`.
It takes the value zero at zero; for non-zero argument `a : α`, it is `1`
if `a` is a square, otherwise it is `-1`.

This only deserves the name "character" when it is multiplicative,
e.g., when `α` is a finite field. See `quadraticCharFun_mul`.

We will later define `quadraticChar` to be a multiplicative character
of type `MulChar F ℤ`, when the domain is a finite field `F`.
-/
def quadraticCharFun (α : Type*) [MonoidWithZero α] [DecidableEq α]
    [DecidablePred (IsSquare : α → Prop)] (a : α) : ℤ :=
  if a = 0 then 0 else if IsSquare a then 1 else -1

end Define

/-!
### Basic properties of the quadratic character

We prove some properties of the quadratic character.
We work with a finite field `F` here.
The interesting case is when the characteristic of `F` is odd.
-/


section quadraticChar

open MulChar

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Some basic API lemmas -/
/-
**quadraticCharFun_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticCharFun_eq_zero_iff {a : F} : quadraticCharFun F a = 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Some basic API lemmas
-/
theorem quadraticCharFun_eq_zero_iff {a : F} : quadraticCharFun F a = 0 ↔ a = 0 := by
  simp only [quadraticCharFun]
  grind

@[simp]
/-
**quadraticCharFun_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticCharFun_zero : quadraticCharFun F 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
-/
theorem quadraticCharFun_zero : quadraticCharFun F 0 = 0 := by
  simp only [quadraticCharFun, if_true]

@[simp]
/-
**quadraticCharFun_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticCharFun_one : quadraticCharFun F 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem quadraticCharFun_one : quadraticCharFun F 1 = 1 := by
  simp only [quadraticCharFun, one_ne_zero, IsSquare.one, if_true, if_false]

/-- If `ringChar F = 2`, then `quadraticCharFun F` takes the value `1` on nonzero elements. -/
/-
**quadraticCharFun_eq_one_of_char_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticCharFun_eq_one_of_char_two (hF : ringChar F = 2) {a : F} (ha : a 
!= 0) : quadraticCharFun F a = 1
参数：hF : ringChar F = 2；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `FiniteField.isSquare_of_char_two`：isSquare_of_char_two (hF : ringChar F 
= 2) (a : F) : IsSquare a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `ringChar F = 2`, then `quadraticCharFun F` takes the value `1` on nonzero el
ements.
-/
theorem quadraticCharFun_eq_one_of_char_two (hF : ringChar F = 2) {a : F} (ha : a ≠ 0) :
    quadraticCharFun F a = 1 := by
  simp only [quadraticCharFun, ha, if_false, ite_eq_left_iff]
  exact fun h ↦ (h (FiniteField.isSquare_of_char_two hF a)).elim

/-- If `ringChar F` is odd, then `quadraticCharFun F a` can be computed in
terms of `a ^ (Fintype.card F / 2)`. -/
/-
**quadraticCharFun_eq_pow_of_char_ne_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticCharFun_eq_pow_of_char_ne_two (hF : ringChar F != 2) {a : F} (ha 
: a != 0) : quadraticCharFun F a = if a ^ (Fintype.card F / 2) = 1 then 1 else -
1
参数：hF : ringChar F != 2；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FiniteField.isSquare_iff`：isSquare_iff (hF : ringChar F != 2) {a : F} (h
a : a != 0) : IsSquare a ↔ a ^ (Fintype.card F / 2) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `ringChar F` is odd, then `quadraticCharFun F a` can be computed in
terms of `a ^ (Fintype.card F / 2)`.
-/
theorem quadraticCharFun_eq_pow_of_char_ne_two (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    quadraticCharFun F a = if a ^ (Fintype.card F / 2) = 1 then 1 else -1 := by
  simp only [quadraticCharFun, ha, if_false]
  simp_rw [FiniteField.isSquare_iff hF ha]

/-- The quadratic character is multiplicative. -/
/-
**quadraticCharFun_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticCharFun_mul (a b : F) : quadraticCharFun F (a * b) = quadraticCha
rFun F a * quadraticCharFun F b
参数：a b : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `quadraticCharFun_zero`：quadraticCharFun_zero : quadraticCharFun F 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `quadraticCharFun_eq_one_of_char_two`：quadraticCharFun_eq_one_of_char_two
 (hF : ringChar F = 2) {a : F} (ha : a != 0) : quadraticCharFun F a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `quadraticCharFun_eq_pow_of_char_ne_two`：quadraticCharFun_eq_pow_of_char_
ne_two (hF : ringChar F != 2) {a : F} (ha : a != 0) : quadraticCharFun F a = if 
a ^ (Fintype.card F / 2) = 1…
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `FiniteField.pow_dichotomy`：pow_dichotomy (hF : ringChar F != 2) {a : F} 
(ha : a != 0) : a ^ (Fintype.card F / 2) = 1 ∨ a ^ (Fintype.card F / 2) = -1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用引理 `Ring.neg_one_ne_one_of_char_ne_two`：Ring.neg_one_ne_one_of_char_ne_two {
R : Type*} [NonAssocRing R] [Nontrivial R] (hR : ringChar R != 2) : (-1 : R) != 
1
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a

--- 原说明 ---
The quadratic character is multiplicative.
-/
theorem quadraticCharFun_mul (a b : F) :
    quadraticCharFun F (a * b) = quadraticCharFun F a * quadraticCharFun F b := by
  by_cases ha : a = 0
  · rw [ha, zero_mul, quadraticCharFun_zero, zero_mul]
  -- now `a ≠ 0`
  by_cases hb : b = 0
  · rw [hb, mul_zero, quadraticCharFun_zero, mul_zero]
  -- now `a ≠ 0` and `b ≠ 0`
  have hab := mul_ne_zero ha hb
  by_cases hF : ringChar F = 2
  · -- case `ringChar F = 2`
    rw [quadraticCharFun_eq_one_of_char_two hF ha, quadraticCharFun_eq_one_of_char_two hF hb,
      quadraticCharFun_eq_one_of_char_two hF hab, mul_one]
  · -- case of odd characteristic
    rw [quadraticCharFun_eq_pow_of_char_ne_two hF ha, quadraticCharFun_eq_pow_of_char_ne_two hF hb,
      quadraticCharFun_eq_pow_of_char_ne_two hF hab, mul_pow]
    rcases FiniteField.pow_dichotomy hF hb with hb' | hb'
    · simp only [hb', mul_one, if_true]
    · have h := Ring.neg_one_ne_one_of_char_ne_two hF
      -- `-1 ≠ 1`
      simp only [hb', mul_neg, mul_one, h, if_false]
      rcases FiniteField.pow_dichotomy hF ha with ha' | ha' <;>
        simp only [ha', h, neg_neg, if_true, if_false]

variable (F) in
/-- The quadratic character as a multiplicative character. -/
@[simps]
/-
**quadraticChar** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：quadraticChar : MulChar F Int where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `quadraticCharFun_one`：quadraticCharFun_one : quadraticCharFun F 1 = 1
· 使用定理 `quadraticCharFun_mul`：quadraticCharFun_mul (a b : F) : quadraticCharFun 
F (a * b) = quadraticCharFun F a * quadraticCharFun F b

--- 原说明 ---
The quadratic character as a multiplicative character.
-/
def quadraticChar : MulChar F ℤ where
  toFun := quadraticCharFun F
  map_one' := quadraticCharFun_one
  map_mul' := quadraticCharFun_mul
  map_nonunit' a ha := by rw [of_not_not (mt Ne.isUnit ha)]; exact quadraticCharFun_zero

/-- The value of the quadratic character on `a` is zero iff `a = 0`. -/
/-
**quadraticChar_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticChar_eq_zero_iff {a : F} : quadraticChar F a = 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `quadraticCharFun_eq_zero_iff`：quadraticCharFun_eq_zero_iff {a : F} : qua
draticCharFun F a = 0 ↔ a = 0

--- 原说明 ---
The value of the quadratic character on `a` is zero iff `a = 0`.
-/
theorem quadraticChar_eq_zero_iff {a : F} : quadraticChar F a = 0 ↔ a = 0 :=
  quadraticCharFun_eq_zero_iff
/-
**quadraticChar_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticChar_zero : quadraticChar F 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `quadraticChar_apply`：∀ (F : Type u_1) [inst : Field F] [inst_1 : Fintype
 F] [inst_2 : DecidableEq F] (a : F),   (quadraticChar F) a = quadraticCharFun F
 a
· 使用定理 `quadraticCharFun_zero`：quadraticCharFun_zero : quadraticCharFun F 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem quadraticChar_zero : quadraticChar F 0 = 0 := by
  simp only [quadraticChar_apply, quadraticCharFun_zero]

/-- For nonzero `a : F`, `quadraticChar F a = 1 ↔ IsSquare a`. -/
/-
**quadraticChar_one_iff_isSquare** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticChar_one_iff_isSquare {a : F} (ha : a != 0) : quadraticChar F a =
 1 ↔ IsSquare a
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `quadraticChar_apply`：∀ (F : Type u_1) [inst : Field F] [inst_1 : Fintype
 F] [inst_2 : DecidableEq F] (a : F),   (quadraticChar F) a = quadraticCharFun F
 a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
For nonzero `a : F`, `quadraticChar F a = 1 ↔ IsSquare a`.
-/
theorem quadraticChar_one_iff_isSquare {a : F} (ha : a ≠ 0) :
    quadraticChar F a = 1 ↔ IsSquare a := by
  simp only [quadraticChar_apply, quadraticCharFun, ha, if_false, ite_eq_left_iff,
    imp_false, not_not, reduceCtorEq]

/-- The quadratic character takes the value `1` on nonzero squares. -/
/-
**quadraticChar_sq_one'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticChar_sq_one' {a : F} (ha : a != 0) : quadraticChar F (a ^ 2) = 1
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `quadraticChar_apply`：∀ (F : Type u_1) [inst : Field F] [inst_1 : Fintype
 F] [inst_2 : DecidableEq F] (a : F),   (quadraticChar F) a = quadraticCharFun F
 a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The quadratic character takes the value `1` on nonzero squares.
-/
theorem quadraticChar_sq_one' {a : F} (ha : a ≠ 0) : quadraticChar F (a ^ 2) = 1 := by
  simp only [quadraticChar_apply, quadraticCharFun, sq_eq_zero_iff, ha, IsSquare.sq, if_true,
    if_false]

/-- The square of the quadratic character on nonzero arguments is `1`. -/
/-
**quadraticChar_sq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticChar_sq_one {a : F} (ha : a != 0) : quadraticChar F a ^ 2 = 1
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `quadraticChar_sq_one'`：quadraticChar_sq_one' {a : F} (ha : a != 0) : qua
draticChar F (a ^ 2) = 1

--- 原说明 ---
The square of the quadratic character on nonzero arguments is `1`.
-/
theorem quadraticChar_sq_one {a : F} (ha : a ≠ 0) : quadraticChar F a ^ 2 = 1 := by
  rwa [pow_two, ← map_mul, ← pow_two, quadraticChar_sq_one']

/-- The quadratic character is `1` or `-1` on nonzero arguments. -/
/-
**quadraticChar_dichotomy** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticChar_dichotomy {a : F} (ha : a != 0) : quadraticChar F a = 1 ∨ qu
adraticChar F a = -1
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sq_eq_one_iff`：∀ {R : Type u} [inst : Ring R] {a : R} [NoZeroDivisors R]
, a ^ 2 = 1 ↔ a = 1 ∨ a = -1
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `quadraticChar_sq_one`：quadraticChar_sq_one {a : F} (ha : a != 0) : quadr
aticChar F a ^ 2 = 1

--- 原说明 ---
The quadratic character is `1` or `-1` on nonzero arguments.
-/
theorem quadraticChar_dichotomy {a : F} (ha : a ≠ 0) :
    quadraticChar F a = 1 ∨ quadraticChar F a = -1 :=
  sq_eq_one_iff.1 <| quadraticChar_sq_one ha

/-- The quadratic character is `1` or `-1` on nonzero arguments. -/
/-
**quadraticChar_eq_neg_one_iff_not_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticChar_eq_neg_one_iff_not_one {a : F} (ha : a != 0) : quadraticChar
 F a = -1 ↔ ¬quadraticChar F a = 1
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `quadraticChar_dichotomy`：quadraticChar_dichotomy {a : F} (ha : a != 0) :
 quadraticChar F a = 1 ∨ quadraticChar F a = -1

--- 原说明 ---
The quadratic character is `1` or `-1` on nonzero arguments.
-/
theorem quadraticChar_eq_neg_one_iff_not_one {a : F} (ha : a ≠ 0) :
    quadraticChar F a = -1 ↔ ¬quadraticChar F a = 1 :=
  ⟨fun h ↦ by rw [h]; lia, fun h₂ ↦ (or_iff_right h₂).mp (quadraticChar_dichotomy ha)⟩

/-- For `a : F`, `quadraticChar F a = -1 ↔ ¬ IsSquare a`. -/
/-
**quadraticChar_neg_one_iff_not_isSquare** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticChar_neg_one_iff_not_isSquare {a : F} : quadraticChar F a = -1 ↔ 
¬IsSquare a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulChar.map_zero`：∀ {R' : Type u_2} [inst : CommMonoidWithZero R'] {R : 
Type u_3} [inst_1 : CommMonoidWithZero R] [Nontrivial R]   (χ : MulChar R R'), χ
 0 = 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `quadraticChar_eq_neg_one_iff_not_one`：quadraticChar_eq_neg_one_iff_not_o
ne {a : F} (ha : a != 0) : quadraticChar F a = -1 ↔ ¬quadraticChar F a = 1
· 使用定理 `quadraticChar_one_iff_isSquare`：quadraticChar_one_iff_isSquare {a : F} (
ha : a != 0) : quadraticChar F a = 1 ↔ IsSquare a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
For `a : F`, `quadraticChar F a = -1 ↔ ¬ IsSquare a`.
-/
theorem quadraticChar_neg_one_iff_not_isSquare {a : F} : quadraticChar F a = -1 ↔ ¬IsSquare a := by
  by_cases ha : a = 0
  · simp only [ha, MulChar.map_zero, zero_eq_neg, one_ne_zero, IsSquare.zero, not_true]
  · rw [quadraticChar_eq_neg_one_iff_not_one ha, quadraticChar_one_iff_isSquare ha]

/-- If `F` has odd characteristic, then `quadraticChar F` takes the value `-1`. -/
/-
**quadraticChar_exists_neg_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticChar_exists_neg_one (hF : ringChar F != 2) : exists a, quadraticC
har F a = -1
参数：hF : ringChar F != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `quadraticChar_neg_one_iff_not_isSquare`：quadraticChar_neg_one_iff_not_is
Square {a : F} : quadraticChar F a = -1 ↔ ¬IsSquare a
· 使用定理 `FiniteField.exists_nonsquare`：exists_nonsquare (hF : ringChar F != 2) : 
exists a : F, ¬IsSquare a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `F` has odd characteristic, then `quadraticChar F` takes the value `-1`.
-/
theorem quadraticChar_exists_neg_one (hF : ringChar F ≠ 2) : ∃ a, quadraticChar F a = -1 :=
  (FiniteField.exists_nonsquare hF).imp fun _ h₁ ↦ quadraticChar_neg_one_iff_not_isSquare.mpr h₁

/-- If `F` has odd characteristic, then `quadraticChar F` takes the value `-1` on some unit. -/
/-
**quadraticChar_exists_neg_one'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quadraticChar_exists_neg_one' (hF : ringChar F != 2) : exists a : Fˣ, quad
raticChar F a = -1
参数：hF : ringChar F != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用引理 `ne_of_eq_of_ne`：ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ 
: b != c) : a != c
· 使用定理 `MulChar.map_nonunit`：map_nonunit (χ : MulChar R R') {a : R} (ha : ¬IsUni
t a) : χ a = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `zero_eq_neg`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, 0 = 
-a ↔ a = 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `quadraticChar_exists_neg_one`：quadraticChar_exists_neg_one (hF : ringCha
r F != 2) : exists a, quadraticChar F a = -1

--- 原说明 ---
If `F` has odd characteristic, then `quadraticChar F` takes the value `-1` on so
me unit.
-/
lemma quadraticChar_exists_neg_one' (hF : ringChar F ≠ 2) : ∃ a : Fˣ, quadraticChar F a = -1 := by
  refine (fun ⟨a, ha⟩ ↦ ⟨IsUnit.unit ?_, ha⟩) (quadraticChar_exists_neg_one hF)
  contrapose ha
  exact ne_of_eq_of_ne ((quadraticChar F).map_nonunit ha) (mt zero_eq_neg.mp one_ne_zero)

/-- If `ringChar F = 2`, then `quadraticChar F` takes the value `1` on nonzero elements. -/
/-
**quadraticChar_eq_one_of_char_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticChar_eq_one_of_char_two (hF : ringChar F = 2) {a : F} (ha : a != 
0) : quadraticChar F a = 1
参数：hF : ringChar F = 2；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `quadraticCharFun_eq_one_of_char_two`：quadraticCharFun_eq_one_of_char_two
 (hF : ringChar F = 2) {a : F} (ha : a != 0) : quadraticCharFun F a = 1

--- 原说明 ---
If `ringChar F = 2`, then `quadraticChar F` takes the value `1` on nonzero eleme
nts.
-/
theorem quadraticChar_eq_one_of_char_two (hF : ringChar F = 2) {a : F} (ha : a ≠ 0) :
    quadraticChar F a = 1 :=
  quadraticCharFun_eq_one_of_char_two hF ha

/-- If `ringChar F` is odd, then `quadraticChar F a` can be computed in
terms of `a ^ (Fintype.card F / 2)`. -/
/-
**quadraticChar_eq_pow_of_char_ne_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticChar_eq_pow_of_char_ne_two (hF : ringChar F != 2) {a : F} (ha : a
 != 0) : quadraticChar F a = if a ^ (Fintype.card F / 2) = 1 then 1 else -1
参数：hF : ringChar F != 2；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `quadraticCharFun_eq_pow_of_char_ne_two`：quadraticCharFun_eq_pow_of_char_
ne_two (hF : ringChar F != 2) {a : F} (ha : a != 0) : quadraticCharFun F a = if 
a ^ (Fintype.card F / 2) = 1…

--- 原说明 ---
If `ringChar F` is odd, then `quadraticChar F a` can be computed in
terms of `a ^ (Fintype.card F / 2)`.
-/
theorem quadraticChar_eq_pow_of_char_ne_two (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    quadraticChar F a = if a ^ (Fintype.card F / 2) = 1 then 1 else -1 :=
  quadraticCharFun_eq_pow_of_char_ne_two hF ha
/-
**quadraticChar_eq_pow_of_char_ne_two'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticChar_eq_pow_of_char_ne_two' (hF : ringChar F != 2) (a : F) : (qua
draticChar F a : F) = a ^ (Fintype.card F / 2)
参数：hF : ringChar F != 2；a : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.div_pos`：∀ {b a : ℕ}, b ≤ a → 0 < b → 0 < a / b
· 使用定理 `Fintype.one_lt_card`：one_lt_card [h : Nontrivial α] : 1 < Fintype.card α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `quadraticChar_apply`：∀ (F : Type u_1) [inst : Field F] [inst_1 : Fintype
 F] [inst_2 : DecidableEq F] (a : F),   (quadraticChar F) a = quadraticCharFun F
 a
· 使用定理 `quadraticCharFun_zero`：quadraticCharFun_zero : quadraticCharFun F 0 = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `quadraticChar_eq_pow_of_char_ne_two`：quadraticChar_eq_pow_of_char_ne_two
 (hF : ringChar F != 2) {a : F} (ha : a != 0) : quadraticChar F a = if a ^ (Fint
ype.card F / 2) = 1 then …
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `FiniteField.pow_dichotomy`：pow_dichotomy (hF : ringChar F != 2) {a : F} 
(ha : a != 0) : a ^ (Fintype.card F / 2) = 1 ∨ a ^ (Fintype.card F / 2) = -1
· 使用定理 `Int.cast_ite`：cast_ite [IntCast R] (P : Prop) [Decidable P] (m n : Int) 
: ((ite P m n : Int) : R) = ite P (m : R) (n : R)
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem quadraticChar_eq_pow_of_char_ne_two' (hF : ringChar F ≠ 2) (a : F) :
    (quadraticChar F a : F) = a ^ (Fintype.card F / 2) := by
  by_cases ha : a = 0
  · have : 0 < Fintype.card F / 2 := Nat.div_pos Fintype.one_lt_card two_pos
    simp only [ha, quadraticChar_apply, quadraticCharFun_zero, Int.cast_zero, zero_pow this.ne']
  · rw [quadraticChar_eq_pow_of_char_ne_two hF ha]
    by_cases ha' : a ^ (Fintype.card F / 2) = 1
    · simp only [ha', if_true, Int.cast_one]
    · have ha'' := Or.resolve_left (FiniteField.pow_dichotomy hF ha) ha'
      simp only [ha'', Int.cast_ite, Int.cast_one, Int.cast_neg, ite_eq_right_iff]
      exact Eq.symm

variable (F) in
/-- The quadratic character is quadratic as a multiplicative character. -/
/-
**quadraticChar_isQuadratic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticChar_isQuadratic : (quadraticChar F).IsQuadratic
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `quadraticChar_zero`：quadraticChar_zero : quadraticChar F 0 = 0
· 使用定理 `quadraticChar_dichotomy`：quadraticChar_dichotomy {a : F} (ha : a != 0) :
 quadraticChar F a = 1 ∨ quadraticChar F a = -1

--- 原说明 ---
The quadratic character is quadratic as a multiplicative character.
-/
theorem quadraticChar_isQuadratic : (quadraticChar F).IsQuadratic := by
  intro a
  by_cases ha : a = 0
  · left; rw [ha]; exact quadraticChar_zero
  · right; exact quadraticChar_dichotomy ha

/-- The quadratic character is nontrivial as a multiplicative character
when the domain has odd characteristic. -/
/-
**quadraticChar_ne_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticChar_ne_one (hF : ringChar F != 2) : quadraticChar F != 1
参数：hF : ringChar F != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `quadraticChar_exists_neg_one'`：quadraticChar_exists_neg_one' (hF : ringC
har F != 2) : exists a : Fˣ, quadraticChar F a = -1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MulChar.one_apply`：one_apply {x : R} (hx : IsUnit x) : (1 : MulChar R R'
) x = 1
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))

--- 原说明 ---
The quadratic character is nontrivial as a multiplicative character
when the domain has odd characteristic.
-/
theorem quadraticChar_ne_one (hF : ringChar F ≠ 2) : quadraticChar F ≠ 1 := by
  rcases quadraticChar_exists_neg_one' hF with ⟨a, ha⟩
  intro hχ
  simp only [hχ, one_apply a.isUnit, reduceCtorEq] at ha

open Finset in
/-- The number of solutions to `x^2 = a` is determined by the quadratic character. -/
/-
**quadraticChar_card_sqrts** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticChar_card_sqrts (hF : ringChar F != 2) (a : F) : #{x : F | x ^ 2 
= a}.toFinset = quadraticChar F a + 1
参数：hF : ringChar F != 2；a : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulChar.map_zero`：∀ {R' : Type u_2} [inst : CommMonoidWithZero R'] {R : 
Type u_3} [inst_1 : CommMonoidWithZero R] [Nontrivial R]   (χ : MulChar R R'), χ
 0 = 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `quadraticChar_one_iff_isSquare`：quadraticChar_one_iff_isSquare {a : F} (
ha : a != 0) : quadraticChar F a = 1 ↔ IsSquare a
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Set.toFinset_ofPred`：toFinset_ofPred [Fintype α] (p : α -> Prop) [Decida
blePred p] [Fintype { x | p x }] : Set.toFinset {x | p x} = Finset.univ.filter p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `List.toFinset_cons`：toFinset_cons : toFinset (a :: l) = insert a (toFins
et l)
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Finset.instLawfulSingleton`：∀ {α : Type u_1} [inst : DecidableEq α], Law
fulSingleton α (Finset α)
· 使用引理 `sq_eq_sq_iff_eq_or_eq_neg`：sq_eq_sq_iff_eq_or_eq_neg : a ^ 2 = b ^ 2 ↔ a
 = b ∨ a = -b
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `List.toFinset_nil`：toFinset_nil : toFinset (@nil α) = ∅
· 使用定理 `Finset.card_pair`：∀ {α : Type u_1} {a b : α} [inst : DecidableEq α], a ≠
 b → {a, b}.card = 2
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
The number of solutions to `x^2 = a` is determined by the quadratic character.
-/
theorem quadraticChar_card_sqrts (hF : ringChar F ≠ 2) (a : F) :
    #{x : F | x ^ 2 = a}.toFinset = quadraticChar F a + 1 := by
  -- we consider the cases `a = 0`, `a` is a nonzero square and `a` is a nonsquare in turn
  by_cases h₀ : a = 0
  · simp only [h₀, sq_eq_zero_iff, Set.ofPred_eq_eq_singleton, Set.toFinset_card,
    Set.card_singleton, Int.natCast_succ, Int.ofNat_zero, MulChar.map_zero]
  · set s := {x : F | x ^ 2 = a}.toFinset
    by_cases h : IsSquare a
    · rw [(quadraticChar_one_iff_isSquare h₀).mpr h]
      rcases h with ⟨b, h⟩
      rw [h, mul_self_eq_zero] at h₀
      have h₁ : s = [b, -b].toFinset := by
        ext1
        rw [← pow_two] at h
        simp_rw [s, Set.toFinset_ofPred, mem_filter_univ, h, List.toFinset_cons, List.toFinset_nil,
          insert_empty_eq, mem_insert, mem_singleton]
        exact sq_eq_sq_iff_eq_or_eq_neg
      norm_cast
      rw [h₁, List.toFinset_cons, List.toFinset_cons, List.toFinset_nil]
      exact card_pair (Ne.symm (mt (Ring.eq_self_iff_eq_zero_of_char_ne_two hF).mp h₀))
    · rw [quadraticChar_neg_one_iff_not_isSquare.mpr h]
      simp only [neg_add_cancel, Int.natCast_eq_zero, card_eq_zero, eq_empty_iff_forall_notMem]
      simpa [s, isSquare_iff_exists_sq, eq_comm] using h

/-- The sum over the values of the quadratic character is zero when the characteristic is odd. -/
/-
**quadraticChar_sum_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticChar_sum_zero (hF : ringChar F != 2) : ∑ a : F, quadraticChar F a
 = 0
参数：hF : ringChar F != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulChar.sum_eq_zero_of_ne_one`：sum_eq_zero_of_ne_one [IsDomain R'] {χ : 
MulChar R R'} (hχ : χ != 1) : ∑ a, χ a = 0
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `quadraticChar_ne_one`：quadraticChar_ne_one (hF : ringChar F != 2) : quad
raticChar F != 1

--- 原说明 ---
The sum over the values of the quadratic character is zero when the characterist
ic is odd.
-/
theorem quadraticChar_sum_zero (hF : ringChar F ≠ 2) : ∑ a : F, quadraticChar F a = 0 :=
  sum_eq_zero_of_ne_one (quadraticChar_ne_one hF)

end quadraticChar

/-!
### Special values of the quadratic character

We express `quadraticChar F (-1)` in terms of `χ₄`.
-/


section SpecialValues

open ZMod MulChar

variable {F : Type*} [Field F] [Fintype F]

/-- The value of the quadratic character at `-1` -/
/-
**quadraticChar_neg_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticChar_neg_one [DecidableEq F] (hF : ringChar F != 2) : quadraticCh
ar F (-1) = χ₄ (Fintype.card F)
参数：hF : ringChar F != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `quadraticChar_eq_pow_of_char_ne_two`：quadraticChar_eq_pow_of_char_ne_two
 (hF : ringChar F != 2) {a : F} (ha : a != 0) : quadraticChar F a = if a ^ (Fint
ype.card F / 2) = 1 then …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.χ₄_eq_neg_one_pow`：χ₄_eq_neg_one_pow {n : Nat} (hn : n % 2 = 1) : χ
₄ n = (-1) ^ (n / 2)
· 使用定理 `FiniteField.odd_card_of_char_ne_two`：odd_card_of_char_ne_two (hF : ringC
har F != 2) : Fintype.card F % 2 = 1
· 使用引理 `Nat.even_or_odd`：even_or_odd (n : Nat) : Even n ∨ Odd n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Even.neg_one_pow`：Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `Odd.neg_one_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistrib
Neg α] {n : ℕ}, Odd n → (-1) ^ n = -1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `Ring.neg_one_ne_one_of_char_ne_two`：Ring.neg_one_ne_one_of_char_ne_two {
R : Type*} [NonAssocRing R] [Nontrivial R] (hR : ringChar R != 2) : (-1 : R) != 
1

--- 原说明 ---
The value of the quadratic character at `-1`
-/
theorem quadraticChar_neg_one [DecidableEq F] (hF : ringChar F ≠ 2) :
    quadraticChar F (-1) = χ₄ (Fintype.card F) := by
  have h := quadraticChar_eq_pow_of_char_ne_two hF (neg_ne_zero.mpr one_ne_zero)
  rw [h, χ₄_eq_neg_one_pow (FiniteField.odd_card_of_char_ne_two hF)]
  generalize Fintype.card F / 2 = n
  rcases Nat.even_or_odd n with h₂ | h₂
  · simp only [Even.neg_one_pow h₂, if_true]
  · simp only [Odd.neg_one_pow h₂, Ring.neg_one_ne_one_of_char_ne_two hF, ite_false]

/-- `-1` is a square in `F` iff `#F` is not congruent to `3` mod `4`. -/
/-
**FiniteField.isSquare_neg_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteField.isSquare_neg_one_iff : IsSquare (-1 : F) ↔ Fintype.card F % 4 
!= 3
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `FiniteField.isSquare_of_char_two`：isSquare_of_char_two (hF : ringChar F 
= 2) (a : F) : IsSquare a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.odd_of_mod_four_eq_three`：odd_of_mod_four_eq_three {n : Nat} : n % 4
 = 3 -> n % 2 = 1
· 使用定理 `FiniteField.even_card_of_char_two`：even_card_of_char_two (hF : ringChar 
F = 2) : Fintype.card F % 2 = 0
· 使用定理 `FiniteField.odd_card_of_char_ne_two`：odd_card_of_char_ne_two (hF : ringC
har F != 2) : Fintype.card F % 2 = 1
· 使用定理 `quadraticChar_one_iff_isSquare`：quadraticChar_one_iff_isSquare {a : F} (
ha : a != 0) : quadraticChar F a = 1 ↔ IsSquare a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用引理 `one_ne_zero'`：one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `quadraticChar_neg_one`：quadraticChar_neg_one [DecidableEq F] (hF : ringC
har F != 2) : quadraticChar F (-1) = χ₄ (Fintype.card F)
· 使用定理 `ZMod.χ₄_nat_eq_if_mod_four`：χ₄_nat_eq_if_mod_four (n : Nat) : χ₄ n = if 
n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1

--- 原说明 ---
`-1` is a square in `F` iff `#F` is not congruent to `3` mod `4`.
-/
theorem FiniteField.isSquare_neg_one_iff : IsSquare (-1 : F) ↔ Fintype.card F % 4 ≠ 3 := by
  classical -- suggested by the linter (instead of `[DecidableEq F]`)
  by_cases hF : ringChar F = 2
  · simp only [FiniteField.isSquare_of_char_two hF, Ne, true_iff]
    exact fun hf ↦
      one_ne_zero <|
        (Nat.odd_of_mod_four_eq_three hf).symm.trans <| FiniteField.even_card_of_char_two hF
  · have h₁ := FiniteField.odd_card_of_char_ne_two hF
    rw [← quadraticChar_one_iff_isSquare (neg_ne_zero.mpr (one_ne_zero' F)),
      quadraticChar_neg_one hF, χ₄_nat_eq_if_mod_four, h₁]
    lia

end SpecialValues

