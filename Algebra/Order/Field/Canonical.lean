/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Ring.Canonical

/-!
# Canonically ordered semifields
-/

public section

variable {α : Type*} [Semifield α] [LinearOrder α] [CanonicallyOrderedAdd α]

-- See note [reducible non-instances]
/--
Definition of `CanonicallyOrderedAdd.toLinearOrderedCommGroupWithZero` / `CanonicallyOrderedAdd.toLinearOrderedCommGroupWithZero` 的定义

English:
abbreviation CanonicallyOrderedAdd.toLinearOrderedCommGroupWithZero
  signature: :
  body: 0
  bot_le _ := zero_le
  isBot_zero _ := zero_le
  mul_lt_mul_of_pos_left _a ha _b _c hbc :=
    have : PosMulStrictMono α := PosMulReflectLT.toPosMulStrictMono _
    mul_lt_mul_of_pos_left hbc ha

中文:
缩写 CanonicallyOrderedAdd.toLinearOrderedCommGroupWithZero
  签名: :
  定义体: 0
  bot_le _ := zero_le
  isBot_zero _ := zero_le
  mul_lt_mul_of_pos_left _a ha _b _c hbc :=
    have : PosMulStrictMono α := PosMulReflectLT.toPosMulStrictMono _
    mul_lt_mul_of_pos_left hbc ha
-/
abbrev CanonicallyOrderedAdd.toLinearOrderedCommGroupWithZero :
    LinearOrderedCommGroupWithZero α where
  bot := 0
  bot_le _ := zero_le
  isBot_zero _ := zero_le
  mul_lt_mul_of_pos_left _a ha _b _c hbc :=
    have : PosMulStrictMono α := PosMulReflectLT.toPosMulStrictMono _
    mul_lt_mul_of_pos_left hbc ha

variable [IsStrictOrderedRing α] [Sub α] [OrderedSub α]

/--
theorem `tsub_div` / 定理 `tsub_div`

English:
theorem tsub_div
  given: (a b c : α)
  statement: (a - b) / c = a / c - b / c
  proof: by simp_rw [div_eq_mul_inv, tsub_mul]

中文:
定理 tsub_div
  条件: (a b c : α)
  结论: (a - b) / c = a / c - b / c
  证明: by simp_rw [div_eq_mul_inv, tsub_mul]

Depends on / 依赖: div_eq_mul_inv, simp_rw, tsub_mul
-/
theorem tsub_div (a b c : α) : (a - b) / c = a / c - b / c := by simp_rw [div_eq_mul_inv, tsub_mul]
