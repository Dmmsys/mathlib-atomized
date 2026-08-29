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

/--
Instance `instAddMonoidWithOne` / 实例 `instAddMonoidWithOne`

English:
instance instAddMonoidWithOne
  signature: : AddMonoidWithOne Nat where
  body: n
  natCast_zero := rfl
  natCast_succ _ := rfl

中文:
实例 instAddMonoidWithOne
  签名: : AddMonoidWithOne 自然数 where
  定义体: n
  natCast_zero := rfl
  natCast_succ _ := rfl
-/
instance instAddMonoidWithOne : AddMonoidWithOne Nat where
  natCast n := n
  natCast_zero := rfl
  natCast_succ _ := rfl

/--
Instance `instAddCommMonoidWithOne` / 实例 `instAddCommMonoidWithOne`

English:
instance instAddCommMonoidWithOne
  signature: : AddCommMonoidWithOne Nat where
  body: instAddMonoidWithOne
  __ := instAddCommMonoid

中文:
实例 instAddCommMonoidWithOne
  签名: : AddCommMonoidWithOne 自然数 where
  定义体: instAddMonoidWithOne
  __ := instAddCommMonoid

Depends on / 依赖: instAddMonoidWithOne
-/
instance instAddCommMonoidWithOne : AddCommMonoidWithOne Nat where
  __ := instAddMonoidWithOne
  __ := instAddCommMonoid

/--
Instance `instDistrib` / 实例 `instDistrib`

English:
instance instDistrib
  signature: : Distrib Nat where
  body: Nat.left_distrib
  right_distrib := Nat.right_distrib

中文:
实例 instDistrib
  签名: : Distrib 自然数 where
  定义体: Nat.left_distrib
  right_distrib := Nat.right_distrib

Depends on / 依赖: Nat.left_distrib, left_distrib
-/
instance instDistrib : Distrib Nat where
  left_distrib := Nat.left_distrib
  right_distrib := Nat.right_distrib

/--
Instance `instNonUnitalNonAssocSemiring` / 实例 `instNonUnitalNonAssocSemiring`

English:
instance instNonUnitalNonAssocSemiring
  signature: : NonUnitalNonAssocSemiring Nat where
  body: instAddCommMonoid
  __ := instDistrib
  __ := instMulZeroClass

中文:
实例 instNonUnitalNonAssocSemiring
  签名: : NonUnitalNonAssocSemiring 自然数 where
  定义体: instAddCommMonoid
  __ := instDistrib
  __ := instMulZeroClass

Depends on / 依赖: instAddCommMonoid
-/
instance instNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring Nat where
  __ := instAddCommMonoid
  __ := instDistrib
  __ := instMulZeroClass

/--
Instance `instNonUnitalSemiring` / 实例 `instNonUnitalSemiring`

English:
instance instNonUnitalSemiring
  signature: : NonUnitalSemiring Nat where
  body: instNonUnitalNonAssocSemiring
  __ := instSemigroupWithZero

中文:
实例 instNonUnitalSemiring
  签名: : NonUnitalSemiring 自然数 where
  定义体: instNonUnitalNonAssocSemiring
  __ := instSemigroupWithZero

Depends on / 依赖: instNonUnitalNonAssocSemiring
-/
instance instNonUnitalSemiring : NonUnitalSemiring Nat where
  __ := instNonUnitalNonAssocSemiring
  __ := instSemigroupWithZero

/--
Instance `instNonAssocSemiring` / 实例 `instNonAssocSemiring`

English:
instance instNonAssocSemiring
  signature: : NonAssocSemiring Nat where
  body: instNonUnitalNonAssocSemiring
  __ := instMulZeroOneClass
  __ := instAddCommMonoidWithOne

中文:
实例 instNonAssocSemiring
  签名: : NonAssocSemiring 自然数 where
  定义体: instNonUnitalNonAssocSemiring
  __ := instMulZeroOneClass
  __ := instAddCommMonoidWithOne

Depends on / 依赖: instNonUnitalNonAssocSemiring
-/
instance instNonAssocSemiring : NonAssocSemiring Nat where
  __ := instNonUnitalNonAssocSemiring
  __ := instMulZeroOneClass
  __ := instAddCommMonoidWithOne

/--
Instance `instSemiring` / 实例 `instSemiring`

English:
instance instSemiring
  signature: : Semiring Nat where
  body: instNonUnitalSemiring
  __ := instNonAssocSemiring
  __ := instMonoidWithZero

中文:
实例 instSemiring
  签名: : Semiring 自然数 where
  定义体: instNonUnitalSemiring
  __ := instNonAssocSemiring
  __ := instMonoidWithZero

Depends on / 依赖: instNonUnitalSemiring
-/
instance instSemiring : Semiring Nat where
  __ := instNonUnitalSemiring
  __ := instNonAssocSemiring
  __ := instMonoidWithZero

/--
Instance `instCommSemiring` / 实例 `instCommSemiring`

English:
instance instCommSemiring
  signature: : CommSemiring Nat where
  body: instSemiring
  __ := instCommMonoid

中文:
实例 instCommSemiring
  签名: : CommSemiring 自然数 where
  定义体: instSemiring
  __ := instCommMonoid

Depends on / 依赖: instSemiring
-/
instance instCommSemiring : CommSemiring Nat where
  __ := instSemiring
  __ := instCommMonoid

/--
Instance `instCharZero` / 实例 `instCharZero`

English:
instance instCharZero
  signature: : CharZero Nat where cast_injective
  body: Function.injective_id

中文:
实例 instCharZero
  签名: : CharZero 自然数 where cast_injective
  定义体: Function.injective_id

Depends on / 依赖: Function, Function.injective_id, injective_id
-/
instance instCharZero : CharZero Nat where cast_injective := Function.injective_id

/--
Instance `instIsDomain` / 实例 `instIsDomain`

English:
instance instIsDomain
  signature: : IsDomain Nat where

中文:
实例 instIsDomain
  签名: : IsDomain 自然数 where
-/
instance instIsDomain : IsDomain Nat where

end Nat
