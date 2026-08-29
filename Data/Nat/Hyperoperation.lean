/-
Copyright (c) 2023 Mark Andrew Gerads. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Andrew Gerads, Junyan Xu, Eric Wieser
-/
module

public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

/-!
# Hyperoperation sequence

This file defines the Hyperoperation sequence.
`hyperoperation 0 m k = k + 1`
`hyperoperation 1 m k = m + k`
`hyperoperation 2 m k = m * k`
`hyperoperation 3 m k = m ^ k`
`hyperoperation (n + 3) m 0 = 1`
`hyperoperation (n + 1) m (k + 1) = hyperoperation n m (hyperoperation (n + 1) m k)`

## References

* <https://en.wikipedia.org/wiki/Hyperoperation>

## Tags

hyperoperation
-/

@[expose] public section


/--
Definition of `hyperoperation` / `hyperoperation` 的定义

English:
definition hyperoperation
  signature: : Nat -> Nat -> Nat -> Nat

中文:
定义 hyperoperation
  签名: : 自然数 -> 自然数 -> 自然数 -> 自然数
-/
def hyperoperation : Nat -> Nat -> Nat -> Nat
  | 0, _, k => k + 1
  | 1, m, 0 => m
  | 2, _, 0 => 0
  | _ + 3, _, 0 => 1
  | n + 1, m, k + 1 => hyperoperation n m (hyperoperation (n + 1) m k)

attribute [local grind] hyperoperation

-- Basic hyperoperation lemmas
@[simp, grind =]
/--
theorem `hyperoperation_zero` / 定理 `hyperoperation_zero`

English:
theorem hyperoperation_zero
  given: (m k : Nat)
  statement: hyperoperation 0 m k = k + 1
  proof: by
  grind

@[grind =]

中文:
定理 hyperoperation_zero
  条件: (m k : 自然数)
  结论: hyperoperation 0 m k = k + 1
  证明: by
  grind

@[grind =]
-/
theorem hyperoperation_zero (m k : Nat) : hyperoperation 0 m k = k + 1 := by
  grind

@[grind =]
/--
theorem `hyperoperation_ge_three_eq_one` / 定理 `hyperoperation_ge_three_eq_one`

English:
theorem hyperoperation_ge_three_eq_one
  given: (n m : Nat)
  statement: hyperoperation (n + 3) m 0 = 1
  proof: by
  grind

@[grind =]

中文:
定理 hyperoperation_ge_three_eq_one
  条件: (n m : 自然数)
  结论: hyperoperation (n + 3) m 0 = 1
  证明: by
  grind

@[grind =]
-/
theorem hyperoperation_ge_three_eq_one (n m : Nat) : hyperoperation (n + 3) m 0 = 1 := by
  grind

@[grind =]
/--
theorem `hyperoperation_recursion` / 定理 `hyperoperation_recursion`

English:
theorem hyperoperation_recursion
  given: (n m k : Nat)
  proof: by
  grind

中文:
定理 hyperoperation_recursion
  条件: (n m k : 自然数)
  证明: by
  grind
-/
theorem hyperoperation_recursion (n m k : Nat) :
    hyperoperation (n + 1) m (k + 1) = hyperoperation n m (hyperoperation (n + 1) m k) := by
  grind

-- Interesting hyperoperation lemmas
@[simp, grind =]
/--
theorem `hyperoperation_one` / 定理 `hyperoperation_one`

English:
theorem hyperoperation_one
  given: (m k : Nat)
  statement: hyperoperation 1 m k = m + k
  proof: by
  induction k with grind

@[simp, grind =]

中文:
定理 hyperoperation_one
  条件: (m k : 自然数)
  结论: hyperoperation 1 m k = m + k
  证明: by
  induction k with grind

@[simp, grind =]
-/
theorem hyperoperation_one (m k : Nat) : hyperoperation 1 m k = m + k := by
  induction k with grind

@[simp, grind =]
/--
theorem `hyperoperation_two` / 定理 `hyperoperation_two`

English:
theorem hyperoperation_two
  given: (m k : Nat)
  statement: hyperoperation 2 m k = m * k
  proof: by
  induction k with grind

@[simp, grind =]

中文:
定理 hyperoperation_two
  条件: (m k : 自然数)
  结论: hyperoperation 2 m k = m * k
  证明: by
  induction k with grind

@[simp, grind =]
-/
theorem hyperoperation_two (m k : Nat) : hyperoperation 2 m k = m * k := by
  induction k with grind

@[simp, grind =]
/--
theorem `hyperoperation_three` / 定理 `hyperoperation_three`

English:
theorem hyperoperation_three
  given: (m k : Nat)
  statement: hyperoperation 3 m k = m ^ k
  proof: by
  induction k with grind

@[grind =]

中文:
定理 hyperoperation_three
  条件: (m k : 自然数)
  结论: hyperoperation 3 m k = m ^ k
  证明: by
  induction k with grind

@[grind =]
-/
theorem hyperoperation_three (m k : Nat) : hyperoperation 3 m k = m ^ k := by
  induction k with grind

@[grind =]
/--
theorem `hyperoperation_ge_two_eq_self` / 定理 `hyperoperation_ge_two_eq_self`

English:
theorem hyperoperation_ge_two_eq_self
  given: (n m : Nat)
  statement: hyperoperation (n + 2) m 1 = m
  proof: by
  induction n with grind

@[grind =]

中文:
定理 hyperoperation_ge_two_eq_self
  条件: (n m : 自然数)
  结论: hyperoperation (n + 2) m 1 = m
  证明: by
  induction n with grind

@[grind =]
-/
theorem hyperoperation_ge_two_eq_self (n m : Nat) : hyperoperation (n + 2) m 1 = m := by
  induction n with grind

@[grind =]
/--
theorem `hyperoperation_two_two_eq_four` / 定理 `hyperoperation_two_two_eq_four`

English:
theorem hyperoperation_two_two_eq_four
  given: (n : Nat)
  statement: hyperoperation (n + 1) 2 2 = 4
  proof: by
  induction n with grind

@[grind =]

中文:
定理 hyperoperation_two_two_eq_four
  条件: (n : 自然数)
  结论: hyperoperation (n + 1) 2 2 = 4
  证明: by
  induction n with grind

@[grind =]
-/
theorem hyperoperation_two_two_eq_four (n : Nat) : hyperoperation (n + 1) 2 2 = 4 := by
  induction n with grind

@[grind =]
/--
theorem `hyperoperation_ge_three_one` / 定理 `hyperoperation_ge_three_one`

English:
theorem hyperoperation_ge_three_one
  given: (n k : Nat)
  statement: hyperoperation (n + 3) 1 k = 1
  proof: by
  induction n generalizing k with grind [cases Nat]

@[grind =]

中文:
定理 hyperoperation_ge_three_one
  条件: (n k : 自然数)
  结论: hyperoperation (n + 3) 1 k = 1
  证明: by
  induction n generalizing k with grind [cases Nat]

@[grind =]

Depends on / 依赖: generalizing
-/
theorem hyperoperation_ge_three_one (n k : Nat) : hyperoperation (n + 3) 1 k = 1 := by
  induction n generalizing k with grind [cases Nat]

@[grind =]
/--
theorem `hyperoperation_ge_four_zero` / 定理 `hyperoperation_ge_four_zero`

English:
theorem hyperoperation_ge_four_zero
  given: (n k : Nat)
  proof: by
  induction k with grind

中文:
定理 hyperoperation_ge_four_zero
  条件: (n k : 自然数)
  证明: by
  induction k with grind
-/
theorem hyperoperation_ge_four_zero (n k : Nat) :
    hyperoperation (n + 4) 0 k = if Even k then 1 else 0 := by
  induction k with grind
