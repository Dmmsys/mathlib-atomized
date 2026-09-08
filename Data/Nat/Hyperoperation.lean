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


/-- Implementation of the hyperoperation sequence
where `hyperoperation n m k` is the `n`th hyperoperation between `m` and `k`.
-/
/-
**hyperoperation** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ℕ → ℕ → ℕ → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation of the hyperoperation sequence
where `hyperoperation n m k` is the `n`th hyperoperation between `m` and `k`.
-/
def hyperoperation : ℕ → ℕ → ℕ → ℕ
  | 0, _, k => k + 1
  | 1, m, 0 => m
  | 2, _, 0 => 0
  | _ + 3, _, 0 => 1
  | n + 1, m, k + 1 => hyperoperation n m (hyperoperation (n + 1) m k)

attribute [local grind] hyperoperation

-- Basic hyperoperation lemmas
@[simp, grind =]
/-
**hyperoperation_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hyperoperation_zero (m k : Nat) : hyperoperation 0 m k = k + 1
参数：m k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hyperoperation_zero (m k : ℕ) : hyperoperation 0 m k = k + 1 := by
  grind

@[grind =]
/-
**hyperoperation_ge_three_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hyperoperation_ge_three_eq_one (n m : Nat) : hyperoperation (n + 3) m 0 = 
1
参数：n m : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hyperoperation_ge_three_eq_one (n m : ℕ) : hyperoperation (n + 3) m 0 = 1 := by
  grind

@[grind =]
/-
**hyperoperation_recursion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hyperoperation_recursion (n m k : Nat) : hyperoperation (n + 1) m (k + 1) 
= hyperoperation n m (hyperoperation (n + 1) m k)
参数：n m k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hyperoperation_recursion (n m k : ℕ) :
    hyperoperation (n + 1) m (k + 1) = hyperoperation n m (hyperoperation (n + 1) m k) := by
  grind

-- Interesting hyperoperation lemmas
@[simp, grind =]
/-
**hyperoperation_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hyperoperation_one (m k : Nat) : hyperoperation 1 m k = m + k
参数：m k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hyperoperation_one (m k : ℕ) : hyperoperation 1 m k = m + k := by
  induction k with grind

@[simp, grind =]
/-
**hyperoperation_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hyperoperation_two (m k : Nat) : hyperoperation 2 m k = m * k
参数：m k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hyperoperation_two (m k : ℕ) : hyperoperation 2 m k = m * k := by
  induction k with grind

@[simp, grind =]
/-
**hyperoperation_three** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hyperoperation_three (m k : Nat) : hyperoperation 3 m k = m ^ k
参数：m k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hyperoperation_three (m k : ℕ) : hyperoperation 3 m k = m ^ k := by
  induction k with grind

@[grind =]
/-
**hyperoperation_ge_two_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hyperoperation_ge_two_eq_self (n m : Nat) : hyperoperation (n + 2) m 1 = m
参数：n m : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hyperoperation_ge_two_eq_self (n m : ℕ) : hyperoperation (n + 2) m 1 = m := by
  induction n with grind

@[grind =]
/-
**hyperoperation_two_two_eq_four** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hyperoperation_two_two_eq_four (n : Nat) : hyperoperation (n + 1) 2 2 = 4
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hyperoperation_two_two_eq_four (n : ℕ) : hyperoperation (n + 1) 2 2 = 4 := by
  induction n with grind

@[grind =]
/-
**hyperoperation_ge_three_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hyperoperation_ge_three_one (n k : Nat) : hyperoperation (n + 3) 1 k = 1
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hyperoperation_ge_three_one (n k : ℕ) : hyperoperation (n + 3) 1 k = 1 := by
  induction n generalizing k with grind [cases Nat]

@[grind =]
/-
**hyperoperation_ge_four_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hyperoperation_ge_four_zero (n k : Nat) : hyperoperation (n + 4) 0 k = if 
Even k then 1 else 0
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hyperoperation_ge_four_zero (n k : ℕ) :
    hyperoperation (n + 4) 0 k = if Even k then 1 else 0 := by
  induction k with grind
