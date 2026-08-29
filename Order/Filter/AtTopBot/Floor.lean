/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Order.Filter.AtTopBot.Finite
public import Mathlib.Tactic.Positivity.Basic

/-!
# `a * c ^ n < (n - d)!` holds true for sufficiently large `n`.
-/

public section

open Filter
open scoped Nat

variable {K : Type*} [Ring K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]

/--
theorem `FloorSemiring.eventually_mul_pow_lt_factorial_sub` / 定理 `FloorSemiring.eventually_mul_pow_lt_factorial_sub`

English:
theorem FloorSemiring.eventually_mul_pow_lt_factorial_sub
  given: (a c : K) (d : Nat)
  proof: by
  filter_upwards [Nat.eventually_mul_pow_lt_factorial_sub ⌈|a|⌉₊ ⌈|c|⌉₊ d] with n h
  calc a * c ^ n
    _ <= |a * c ^ n| := le_abs_self _
    _ <= ⌈|a|⌉₊ * (⌈|c|⌉₊ : K) ^ n := ?_
    _ = ↑(⌈|a|⌉₊ * ⌈|c|⌉₊ ^ n) := ?_
    _ < (n - d)! := Nat.cast_lt.mpr h
  · rw [abs_mul, abs_pow]
    gcongr <;> t

中文:
定理 FloorSemiring.eventually_mul_pow_lt_factorial_sub
  条件: (a c : K) (d : 自然数)
  证明: by
  filter_upwards [Nat.eventually_mul_pow_lt_factorial_sub ⌈|a|⌉₊ ⌈|c|⌉₊ d] with n h
  calc a * c ^ n
    _ <= |a * c ^ n| := le_abs_self _
    _ <= ⌈|a|⌉₊ * (⌈|c|⌉₊ : K) ^ n := ?_
    _ = ↑(⌈|a|⌉₊ * ⌈|c|⌉₊ ^ n) := ?_
    _ < (n - d)! := Nat.cast_lt.mpr h
  · rw [abs_mul, abs_pow]
    gcongr <;> t

Depends on / 依赖: Nat.cast_lt.mpr, Nat.cast_mul, Nat.cast_pow, Nat.eventually_mul_pow_lt_factorial_sub, Nat.le_ceil, abs_mul, abs_pow, cast_lt, cast_mul, cast_pow, eventually_mul_pow_lt_factorial_sub, filter_upwards, le_abs_self, le_ceil, simp_rw
-/
theorem FloorSemiring.eventually_mul_pow_lt_factorial_sub (a c : K) (d : Nat) :
    forallᶠ n in atTop, a * c ^ n < (n - d)! := by
  filter_upwards [Nat.eventually_mul_pow_lt_factorial_sub ⌈|a|⌉₊ ⌈|c|⌉₊ d] with n h
  calc a * c ^ n
    _ <= |a * c ^ n| := le_abs_self _
    _ <= ⌈|a|⌉₊ * (⌈|c|⌉₊ : K) ^ n := ?_
    _ = ↑(⌈|a|⌉₊ * ⌈|c|⌉₊ ^ n) := ?_
    _ < (n - d)! := Nat.cast_lt.mpr h
  · rw [abs_mul, abs_pow]
    gcongr <;> try first | positivity | apply Nat.le_ceil
  · simp_rw [Nat.cast_mul, Nat.cast_pow]
