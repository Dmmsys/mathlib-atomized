/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Tactic.Spread

/-!
# The natural numbers form a cancellative `CommMonoidWithZero`

This file contains the `CommMonoidWithZero` and `IsCancelMulZero` instances on the natural numbers.

See note [foundational algebra order theory].
-/

public section

assert_not_exists Ring

namespace Nat

/-
**Nat.instMulZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instMulZeroClass : MulZeroClass Nat where zero_mul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zero_mul`：∀ (n : ℕ), 0 * n = 0
· 使用定理 `Nat.mul_zero`：∀ (n : ℕ), n * 0 = 0
-/
instance instMulZeroClass : MulZeroClass ℕ where
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero
/-
**Nat.instSemigroupWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instSemigroupWithZero : SemigroupWithZero Nat where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
instance instSemigroupWithZero : SemigroupWithZero ℕ where
  __ := instSemigroup
  __ := instMulZeroClass
/-
**Nat.instMonoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instMonoidWithZero : MonoidWithZero Nat where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
instance instMonoidWithZero : MonoidWithZero ℕ where
  __ := instMonoid
  __ := instMulZeroClass
  __ := instSemigroupWithZero
/-
**Nat.instCommMonoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instCommMonoidWithZero : CommMonoidWithZero Nat where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZero.zero_mul`：∀ {M₀ : Type u} [self : MonoidWithZero M₀] (a :
 M₀), 0 * a = 0
· 使用定理 `MonoidWithZero.mul_zero`：∀ {M₀ : Type u} [self : MonoidWithZero M₀] (a :
 M₀), a * 0 = 0
-/
instance instCommMonoidWithZero : CommMonoidWithZero ℕ where
  __ := instCommMonoid
  __ := instMonoidWithZero
/-
**Nat.instIsCancelMulZero** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instIsCancelMulZero : IsCancelMulZero Nat where mul_left_cancel_of_ne_zero
 h _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_of_mul_eq_mul_left`：∀ {m k n : ℕ}, 0 < n → n * m = n * k → m = k
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Nat.eq_of_mul_eq_mul_right`：∀ {n m k : ℕ}, 0 < m → n * m = k * m → n = k
-/
instance instIsCancelMulZero : IsCancelMulZero ℕ where
  mul_left_cancel_of_ne_zero h _ _ := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h)
  mul_right_cancel_of_ne_zero h _ _ := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h)
/-
**Nat.instMulDivCancelClass** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instMulDivCancelClass : MulDivCancelClass Nat where mul_div_cancel _ _b hb
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mul_div_cancel`：∀ (m : ℕ) {n : ℕ}, 0 < n → m * n / n = m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
-/
instance instMulDivCancelClass : MulDivCancelClass ℕ where
  mul_div_cancel _ _b hb := Nat.mul_div_cancel _ (Nat.pos_iff_ne_zero.2 hb)
/-
**Nat.instMulZeroOneClass** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instMulZeroOneClass : MulZeroOneClass Nat where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOneClass.one_mul`：∀ {M : Type u} [self : MulOneClass M] (a : M), 1 * 
a = a
· 使用定理 `MulOneClass.mul_one`：∀ {M : Type u} [self : MulOneClass M] (a : M), a * 
1 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
instance instMulZeroOneClass : MulZeroOneClass ℕ where
  __ := instMulZeroClass
  __ := instMulOneClass

end Nat

