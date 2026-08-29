/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Order.BooleanAlgebra.Set

/-!
# The natural numbers form an ordered semiring

This file contains the commutative linear ordered semiring instance on the natural numbers.

See note [foundational algebra order theory].
-/

public section

namespace Nat


/--
Instance `instIsStrictOrderedRing` / 实例 `instIsStrictOrderedRing`

English:
instance instIsStrictOrderedRing
  signature: : IsStrictOrderedRing Nat where
  body: Nat.mul_lt_mul_of_pos_left hbc ha
  mul_lt_mul_of_pos_right _a ha _b _c hbc := Nat.mul_lt_mul_of_pos_right hbc ha

中文:
实例 instIsStrictOrderedRing
  签名: : 是StrictOrdered环 自然数 where
  定义体: Nat.mul_lt_mul_of_pos_left hbc ha
  mul_lt_mul_of_pos_right _a ha _b _c hbc := Nat.mul_lt_mul_of_pos_right hbc ha

Depends on / 依赖: Nat.mul_lt_mul_of_pos_left, mul_lt_mul_of_pos_left
-/
instance instIsStrictOrderedRing : IsStrictOrderedRing Nat where
  mul_lt_mul_of_pos_left _a ha _b _c hbc := Nat.mul_lt_mul_of_pos_left hbc ha
  mul_lt_mul_of_pos_right _a ha _b _c hbc := Nat.mul_lt_mul_of_pos_right hbc ha

/--
Instance `instLinearOrderedCommMonoidWithZero` / 实例 `instLinearOrderedCommMonoidWithZero`

English:
instance instLinearOrderedCommMonoidWithZero
  signature: : LinearOrderedCommMonoidWithZero Nat where
  body: 0
  bot_le := zero_le
  isBot_zero := zero_le

中文:
实例 instLinearOrderedCommMonoidWithZero
  签名: : 带零LinearOrderedComm幺半群 自然数 where
  定义体: 0
  bot_le := zero_le
  isBot_zero := zero_le
-/
instance instLinearOrderedCommMonoidWithZero : LinearOrderedCommMonoidWithZero Nat where
  bot := 0
  bot_le := zero_le
  isBot_zero := zero_le


/--
lemma `isCompl_even_odd` / 引理 `isCompl_even_odd`

English:
lemma isCompl_even_odd
  statement: IsCompl { n : Nat | Even n } { n | Odd n }
  proof: by
  simp only [← Set.compl_ofPred, isCompl_compl, ← not_even_iff_odd]

中文:
引理 isCompl_even_odd
  结论: 是补集 { n : 自然数 | Even n } { n | Odd n }
  证明: by
  simp only [← Set.compl_ofPred, isCompl_compl, ← not_even_iff_odd]

Depends on / 依赖: Set.compl_ofPred, compl_ofPred, isCompl_compl, not_even_iff_odd
-/
lemma isCompl_even_odd : IsCompl { n : Nat | Even n } { n | Odd n } := by
  simp only [← Set.compl_ofPred, isCompl_compl, ← not_even_iff_odd]

end Nat
