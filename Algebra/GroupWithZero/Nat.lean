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

/--
Instance `instMulZeroClass` / 实例 `instMulZeroClass`

English:
instance instMulZeroClass
  signature: : MulZeroClass Nat where
  body: Nat.zero_mul
  mul_zero := Nat.mul_zero

中文:
实例 instMulZeroClass
  签名: : MulZeroClass 自然数 where
  定义体: Nat.zero_mul
  mul_zero := Nat.mul_zero

Depends on / 依赖: Nat.zero_mul, zero_mul
-/
instance instMulZeroClass : MulZeroClass Nat where
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero

/--
Instance `instSemigroupWithZero` / 实例 `instSemigroupWithZero`

English:
instance instSemigroupWithZero
  signature: : SemigroupWithZero Nat where
  body: instSemigroup
  __ := instMulZeroClass

中文:
实例 instSemigroupWithZero
  签名: : SemigroupWithZero 自然数 where
  定义体: instSemigroup
  __ := instMulZeroClass

Depends on / 依赖: colimit, colimit.isColimit, instSemigroup, isColimit, isColimitCoconeOfHasColimitEval, preservesColimit_of_preserves_colimit_cocone
-/
instance instSemigroupWithZero : SemigroupWithZero Nat where
  __ := instSemigroup
  __ := instMulZeroClass

/--
Instance `instMonoidWithZero` / 实例 `instMonoidWithZero`

English:
instance instMonoidWithZero
  signature: : MonoidWithZero Nat where
  body: instMonoid
  __ := instMulZeroClass
  __ := instSemigroupWithZero

中文:
实例 instMonoidWithZero
  签名: : MonoidWithZero 自然数 where
  定义体: instMonoid
  __ := instMulZeroClass
  __ := instSemigroupWithZero

Depends on / 依赖: instMonoid
-/
instance instMonoidWithZero : MonoidWithZero Nat where
  __ := instMonoid
  __ := instMulZeroClass
  __ := instSemigroupWithZero

/--
Instance `instCommMonoidWithZero` / 实例 `instCommMonoidWithZero`

English:
instance instCommMonoidWithZero
  signature: : CommMonoidWithZero Nat where
  body: instCommMonoid
  __ := instMonoidWithZero

中文:
实例 instCommMonoidWithZero
  签名: : CommMonoidWithZero 自然数 where
  定义体: instCommMonoid
  __ := instMonoidWithZero

Depends on / 依赖: instCommMonoid
-/
instance instCommMonoidWithZero : CommMonoidWithZero Nat where
  __ := instCommMonoid
  __ := instMonoidWithZero

/--
Instance `instIsCancelMulZero` / 实例 `instIsCancelMulZero`

English:
instance instIsCancelMulZero
  signature: : IsCancelMulZero Nat where
  body: Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h)
  mul_right_cancel_of_ne_zero h _ _ := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h)

中文:
实例 instIsCancelMulZero
  签名: : IsCancelMulZero 自然数 where
  定义体: Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h)
  mul_right_cancel_of_ne_zero h _ _ := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h)

Depends on / 依赖: Nat.eq_of_mul_eq_mul_left, Nat.pos_of_ne_zero, eq_of_mul_eq_mul_left, pos_of_ne_zero
-/
instance instIsCancelMulZero : IsCancelMulZero Nat where
  mul_left_cancel_of_ne_zero h _ _ := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h)
  mul_right_cancel_of_ne_zero h _ _ := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h)

/--
Instance `instMulDivCancelClass` / 实例 `instMulDivCancelClass`

English:
instance instMulDivCancelClass
  signature: : MulDivCancelClass Nat where
  body: Nat.mul_div_cancel _ (Nat.pos_iff_ne_zero.2 hb)

中文:
实例 instMulDivCancelClass
  签名: : MulDivCancelClass 自然数 where
  定义体: Nat.mul_div_cancel _ (Nat.pos_iff_ne_zero.2 hb)

Depends on / 依赖: Nat.mul_div_cancel, Nat.pos_iff_ne_zero, mul_div_cancel, pos_iff_ne_zero
-/
instance instMulDivCancelClass : MulDivCancelClass Nat where
  mul_div_cancel _ _b hb := Nat.mul_div_cancel _ (Nat.pos_iff_ne_zero.2 hb)

/--
Instance `instMulZeroOneClass` / 实例 `instMulZeroOneClass`

English:
instance instMulZeroOneClass
  signature: : MulZeroOneClass Nat where
  body: instMulZeroClass
  __ := instMulOneClass

中文:
实例 instMulZeroOneClass
  签名: : MulZeroOneClass 自然数 where
  定义体: instMulZeroClass
  __ := instMulOneClass

Depends on / 依赖: instMulZeroClass
-/
instance instMulZeroOneClass : MulZeroOneClass Nat where
  __ := instMulZeroClass
  __ := instMulOneClass

end Nat
