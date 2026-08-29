/-
Copyright (c) 2023 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Ring

/-!
# Superfactorial

This file defines the [superfactorial](https://en.wikipedia.org/wiki/Superfactorial)
`sf n = 1! * 2! * 3! * ... * n!`.

## Main declarations

* `Nat.superFactorial`: The superfactorial, denoted by `sf`.
-/

@[expose] public section


namespace Nat

/--
Definition of `superFactorial` / `superFactorial` 的定义

English:
definition superFactorial
  signature: : Nat -> Nat

中文:
定义 superFactorial
  签名: : 自然数 -> 自然数
-/
def superFactorial : Nat -> Nat
  | 0 => 1
  | succ n => factorial n.succ * superFactorial n

/-- `sf` notation for superfactorial -/
scoped notation "sf " n:60 => Nat.superFactorial n

section SuperFactorial

@[simp]
/--
theorem `superFactorial_zero` / 定理 `superFactorial_zero`

English:
theorem superFactorial_zero
  statement: sf 0 = 1
  proof: rfl

中文:
定理 superFactorial_zero
  结论: sf 0 = 1
  证明: rfl
-/
theorem superFactorial_zero : sf 0 = 1 :=
  rfl

/--
theorem `superFactorial_succ` / 定理 `superFactorial_succ`

English:
theorem superFactorial_succ
  given: (n : Nat)
  statement: (sf n.succ) = (n + 1)! * sf n
  proof: rfl

@[simp]

中文:
定理 superFactorial_succ
  条件: (n : 自然数)
  结论: (sf n.succ) = (n + 1)! * sf n
  证明: rfl

@[simp]
-/
theorem superFactorial_succ (n : Nat) : (sf n.succ) = (n + 1)! * sf n :=
  rfl

@[simp]
/--
theorem `superFactorial_one` / 定理 `superFactorial_one`

English:
theorem superFactorial_one
  statement: sf 1 = 1
  proof: rfl

@[simp]

中文:
定理 superFactorial_one
  结论: sf 1 = 1
  证明: rfl

@[simp]
-/
theorem superFactorial_one : sf 1 = 1 :=
  rfl

@[simp]
/--
theorem `superFactorial_two` / 定理 `superFactorial_two`

English:
theorem superFactorial_two
  statement: sf 2 = 2
  proof: rfl

中文:
定理 superFactorial_two
  结论: sf 2 = 2
  证明: rfl
-/
theorem superFactorial_two : sf 2 = 2 :=
  rfl

open Finset

@[simp]
/--
theorem `prod_Icc_factorial` / 定理 `prod_Icc_factorial`

English:
theorem prod_Icc_factorial
  statement: forall n : Nat, ∏ x in Icc 1 n, x ! = sf n

中文:
定理 prod_Icc_factorial
  结论: 对任意 n : 自然数, ∏ x in 闭区间 1 n, x ! = sf n
-/
theorem prod_Icc_factorial : forall n : Nat, ∏ x in Icc 1 n, x ! = sf n
  | 0 => rfl
  | n + 1 => by
    rw [← Ico_add_one_right_eq_Icc 1]; rw [prod_Ico_succ_top le_add_self]; rw [Nat.factorial_succ]; rw [Ico_add_one_right_eq_Icc 1 n]; rw [prod_Icc_factorial n]; rw [superFactorial]; rw [factorial]; rw [mul_comm]

@[simp]
/--
theorem `prod_range_factorial_succ` / 定理 `prod_range_factorial_succ`

English:
theorem prod_range_factorial_succ
  given: (n : Nat)
  statement: ∏ x in range n, (x + 1)! = sf n
  proof: prod_Icc_factorial n ▸ range_eq_Ico n ▸ Finset.prod_Ico_add' _ _ _ _

@[simp]

中文:
定理 prod_range_factorial_succ
  条件: (n : 自然数)
  结论: ∏ x in range n, (x + 1)! = sf n
  证明: prod_Icc_factorial n ▸ range_eq_Ico n ▸ Finset.prod_Ico_add' _ _ _ _

@[simp]

Depends on / 依赖: Finset, Finset.prod_Ico_add, prod_Icc_factorial, prod_Ico_add, range_eq_Ico
-/
theorem prod_range_factorial_succ (n : Nat) : ∏ x in range n, (x + 1)! = sf n :=
  prod_Icc_factorial n ▸ range_eq_Ico n ▸ Finset.prod_Ico_add' _ _ _ _

@[simp]
/--
theorem `prod_range_succ_factorial` / 定理 `prod_range_succ_factorial`

English:
theorem prod_range_succ_factorial
  statement: forall n : Nat, ∏ x in range (n + 1), x ! = sf n

中文:
定理 prod_range_succ_factorial
  结论: 对任意 n : 自然数, ∏ x in range (n + 1), x ! = sf n
-/
theorem prod_range_succ_factorial : forall n : Nat, ∏ x in range (n + 1), x ! = sf n
  | 0 => rfl
  | n + 1 => by
    rw [prod_range_succ]; rw [prod_range_succ_factorial n]; rw [mul_comm]; rw [superFactorial]

/--
theorem `superFactorial_two_mul` / 定理 `superFactorial_two_mul`

English:
theorem superFactorial_two_mul
  statement: forall n : Nat,

中文:
定理 superFactorial_two_mul
  结论: 对任意 n : 自然数,
-/
theorem superFactorial_two_mul : forall n : Nat,
    sf (2 * n) = (∏ i in range n, (2 * i + 1)!) ^ 2 * 2 ^ n * n !
  | 0 => rfl
  | (n + 1) => by
    simp only [prod_range_succ, mul_pow, mul_add, mul_one, superFactorial_succ,
      superFactorial_two_mul n, factorial_succ]
    ring

/--
theorem `superFactorial_four_mul` / 定理 `superFactorial_four_mul`

English:
theorem superFactorial_four_mul
  given: (n : Nat)
  proof: calc
    sf (4 * n) = (∏ i in range (2 * n), (2 * i + 1)!) ^ 2 * 2 ^ (2 * n) * (2 * n)! := by
      rw [← superFactorial_two_mul]; rw [← mul_assoc]; rw [Nat.mul_two]
    _ = ((∏ i in range (2 * n), (2 * i + 1)!) * 2 ^ n) ^ 2 * (2 * n)! := by
      rw [pow_mul']; rw [mul_pow]

中文:
定理 superFactorial_four_mul
  条件: (n : 自然数)
  证明: calc
    sf (4 * n) = (∏ i in range (2 * n), (2 * i + 1)!) ^ 2 * 2 ^ (2 * n) * (2 * n)! := by
      rw [← superFactorial_two_mul]; rw [← mul_assoc]; rw [Nat.mul_two]
    _ = ((∏ i in range (2 * n), (2 * i + 1)!) * 2 ^ n) ^ 2 * (2 * n)! := by
      rw [pow_mul']; rw [mul_pow]

Depends on / 依赖: Nat.mul_two, mul_assoc, mul_pow, mul_two, pow_mul, superFactorial_two_mul
-/
theorem superFactorial_four_mul (n : Nat) :
    sf (4 * n) = ((∏ i in range (2 * n), (2 * i + 1)!) * 2 ^ n) ^ 2 * (2 * n)! :=
  calc
    sf (4 * n) = (∏ i in range (2 * n), (2 * i + 1)!) ^ 2 * 2 ^ (2 * n) * (2 * n)! := by
      rw [← superFactorial_two_mul]; rw [← mul_assoc]; rw [Nat.mul_two]
    _ = ((∏ i in range (2 * n), (2 * i + 1)!) * 2 ^ n) ^ 2 * (2 * n)! := by
      rw [pow_mul']; rw [mul_pow]

end SuperFactorial

end Nat
