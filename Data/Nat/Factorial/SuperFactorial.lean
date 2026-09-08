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

/-- `Nat.superFactorial n` is the superfactorial of `n`. -/
/-
**Nat.superFactorial** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：ℕ → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Nat.superFactorial n` is the superfactorial of `n`.
-/
def superFactorial : ℕ → ℕ
  | 0 => 1
  | succ n => factorial n.succ * superFactorial n

/-- `sf` notation for superfactorial -/
scoped notation "sf " n:60 => Nat.superFactorial n

section SuperFactorial

@[simp]
/-
**Nat.superFactorial_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：superFactorial_zero : sf 0 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem superFactorial_zero : sf 0 = 1 :=
  rfl
/-
**Nat.superFactorial_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：superFactorial_succ (n : Nat) : (sf n.succ) = (n + 1)! * sf n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem superFactorial_succ (n : ℕ) : (sf n.succ) = (n + 1)! * sf n :=
  rfl

@[simp]
/-
**Nat.superFactorial_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：superFactorial_one : sf 1 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem superFactorial_one : sf 1 = 1 :=
  rfl

@[simp]
/-
**Nat.superFactorial_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：superFactorial_two : sf 2 = 2
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem superFactorial_two : sf 2 = 2 :=
  rfl

open Finset

@[simp]
/-
**Nat.prod_Icc_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), ∏ x ∈ Finset.Icc 1 n, x.factorial = n.superFactorial
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_Icc_factorial : ∀ n : ℕ, ∏ x ∈ Icc 1 n, x ! = sf n
  | 0 => rfl
  | n + 1 => by
    rw [← Ico_add_one_right_eq_Icc 1, prod_Ico_succ_top le_add_self, Nat.factorial_succ,
      Ico_add_one_right_eq_Icc 1 n, prod_Icc_factorial n, superFactorial, factorial, mul_comm]

@[simp]
/-
**Nat.prod_range_factorial_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_range_factorial_succ (n : Nat) : ∏ x in range n, (x + 1)! = sf n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_Ico_add'`：prod_Ico_add' [AddCommMonoid α] [PartialOrder α] [
IsOrderedCancelAddMonoid α] [ExistsAddOfLE α] [LocallyFiniteOrder α] (f : α -> M
) (a b c :…
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.range_eq_Ico`：∀ (a : ℕ), Finset.range a = Finset.Ico 0 a
· 使用定理 `Nat.prod_Icc_factorial`：∀ (n : ℕ), ∏ x ∈ Finset.Icc 1 n, x.factorial = n
.superFactorial
-/
theorem prod_range_factorial_succ (n : ℕ) : ∏ x ∈ range n, (x + 1)! = sf n :=
  prod_Icc_factorial n ▸ range_eq_Ico n ▸ Finset.prod_Ico_add' _ _ _ _

@[simp]
/-
**Nat.prod_range_succ_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), ∏ x ∈ Finset.range (n + 1), x.factorial = n.superFactorial
参数：n : ℕ；n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_range_succ_factorial : ∀ n : ℕ, ∏ x ∈ range (n + 1), x ! = sf n
  | 0 => rfl
  | n + 1 => by
    rw [prod_range_succ, prod_range_succ_factorial n, mul_comm, superFactorial]
/-
**Nat.superFactorial_two_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), (2 * n).superFactorial = (∏ i ∈ Finset.range n, (2 * i + 1).fac
torial) ^ 2 * 2 ^ n * n.factorial
参数：n : ℕ；2 * n；∏ i ∈ Finset.range n, (2 * i + 1).factorial。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem superFactorial_two_mul : ∀ n : ℕ,
    sf (2 * n) = (∏ i ∈ range n, (2 * i + 1)!) ^ 2 * 2 ^ n * n !
  | 0 => rfl
  | (n + 1) => by
    simp only [prod_range_succ, mul_pow, mul_add, mul_one, superFactorial_succ,
      superFactorial_two_mul n, factorial_succ]
    ring
/-
**Nat.superFactorial_four_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：superFactorial_four_mul (n : Nat) : sf (4 * n) = ((∏ i in range (2 * n), (
2 * i + 1)!) * 2 ^ n) ^ 2 * (2 * n)!
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.superFactorial_two_mul`：∀ (n : ℕ), (2 * n).superFactorial = (∏ i ∈ F
inset.range n, (2 * i + 1).factorial) ^ 2 * 2 ^ n * n.factorial
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.mul_two`：∀ (n : ℕ), n * 2 = n + n
· 使用引理 `pow_mul'`：pow_mul' (a : M) (m n : Nat) : a ^ (m * n) = (a ^ n) ^ m
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
-/
theorem superFactorial_four_mul (n : ℕ) :
    sf (4 * n) = ((∏ i ∈ range (2 * n), (2 * i + 1)!) * 2 ^ n) ^ 2 * (2 * n)! :=
  calc
    sf (4 * n) = (∏ i ∈ range (2 * n), (2 * i + 1)!) ^ 2 * 2 ^ (2 * n) * (2 * n)! := by
      rw [← superFactorial_two_mul, ← mul_assoc, Nat.mul_two]
    _ = ((∏ i ∈ range (2 * n), (2 * i + 1)!) * 2 ^ n) ^ 2 * (2 * n)! := by
      rw [pow_mul', mul_pow]

end SuperFactorial

end Nat

