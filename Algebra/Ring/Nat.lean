/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Basic

/-!
# The natural numbers form a semiring

This file contains the commutative semiring instance on the natural numbers.

See note [foundational algebra order theory].
-/

public section

namespace Nat

/-
**Nat.instAddMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instAddMonoidWithOne : AddMonoidWithOne Nat where natCast n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddMonoidWithOne : AddMonoidWithOne ℕ where
  natCast n := n
  natCast_zero := rfl
  natCast_succ _ := rfl
/-
**Nat.instAddCommMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instAddCommMonoidWithOne : AddCommMonoidWithOne Nat where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommMonoid.add_comm`：∀ {M : Type u} [self : AddCommMonoid M] (a b : M
), a + b = b + a
-/
instance instAddCommMonoidWithOne : AddCommMonoidWithOne ℕ where
  __ := instAddMonoidWithOne
  __ := instAddCommMonoid
/-
**Nat.instDistrib** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instDistrib : Distrib Nat where left_distrib
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.left_distrib`：∀ (n m k : ℕ), n * (m + k) = n * m + n * k
· 使用定理 `Nat.right_distrib`：∀ (n m k : ℕ), (n + m) * k = n * k + m * k
-/
instance instDistrib : Distrib ℕ where
  left_distrib := Nat.left_distrib
  right_distrib := Nat.right_distrib
/-
**Nat.instNonUnitalNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring Nat where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Distrib.left_distrib`：∀ {R : Type u_1} [self : Distrib R] (a b c : R), a
 * (b + c) = a * b + a * c
· 使用定理 `Distrib.right_distrib`：∀ {R : Type u_1} [self : Distrib R] (a b c : R), 
(a + b) * c = a * c + b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
instance instNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring ℕ where
  __ := instAddCommMonoid
  __ := instDistrib
  __ := instMulZeroClass
/-
**Nat.instNonUnitalSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instNonUnitalSemiring : NonUnitalSemiring Nat where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalSemiring : NonUnitalSemiring ℕ where
  __ := instNonUnitalNonAssocSemiring
  __ := instSemigroupWithZero
/-
**Nat.instNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instNonAssocSemiring : NonAssocSemiring Nat where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonAssocSemiring : NonAssocSemiring ℕ where
  __ := instNonUnitalNonAssocSemiring
  __ := instMulZeroOneClass
  __ := instAddCommMonoidWithOne
/-
**Nat.instSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instSemiring : Semiring Nat where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSemiring.mul_assoc`：∀ {α : Type u} [self : NonUnitalSemiring α]
 (a b c : α), a * b * c = a * (b * c)
· 使用定理 `NonAssocSemiring.one_mul`：∀ {α : Type u} [self : NonAssocSemiring α] (a 
: α), 1 * a = a
· 使用定理 `NonAssocSemiring.mul_one`：∀ {α : Type u} [self : NonAssocSemiring α] (a 
: α), a * 1 = a
· 使用定理 `NonAssocSemiring.natCast_zero`：∀ {α : Type u} [self : NonAssocSemiring α
], ↑0 = 0
· 使用定理 `NonAssocSemiring.natCast_succ`：∀ {α : Type u} [self : NonAssocSemiring α
] (n : ℕ), ↑(n + 1) = ↑n + 1
-/
instance instSemiring : Semiring ℕ where
  __ := instNonUnitalSemiring
  __ := instNonAssocSemiring
  __ := instMonoidWithZero
/-
**Nat.instCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instCommSemiring : CommSemiring Nat where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CommMonoid.mul_comm`：∀ {M : Type u} [self : CommMonoid M] (a b : M), a *
 b = b * a
-/
instance instCommSemiring : CommSemiring ℕ where
  __ := instSemiring
  __ := instCommMonoid
/-
**Nat.instCharZero** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instCharZero : CharZero Nat where cast_injective
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
-/
instance instCharZero : CharZero ℕ where cast_injective := Function.injective_id
/-
**Nat.instIsDomain** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：IsDomain ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsDomain : IsDomain ℕ where

end Nat

