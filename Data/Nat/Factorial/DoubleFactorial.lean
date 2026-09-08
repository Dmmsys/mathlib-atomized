/-
Copyright (c) 2023 Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Levinson
-/
module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Double factorials

This file defines the double factorial,
  `n‼ := n * (n - 2) * (n - 4) * ...`.

## Main declarations

* `Nat.doubleFactorial`: The double factorial.
-/

@[expose] public section


open Nat

namespace Nat

/-- `Nat.doubleFactorial n` is the double factorial of `n`. -/
@[simp]
/-
**Nat.doubleFactorial** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：ℕ → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Nat.doubleFactorial n` is the double factorial of `n`.
-/
def doubleFactorial : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | k + 2 => (k + 2) * doubleFactorial k

-- This notation is `\!!` not two !'s
@[inherit_doc] scoped notation:10000 n "‼" => Nat.doubleFactorial n
/-
**Nat.doubleFactorial_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), 0 < n.doubleFactorial
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma doubleFactorial_pos : ∀ n, 0 < n‼
  | 0 | 1 => zero_lt_one
  | _n + 2 => mul_pos (succ_pos _) (doubleFactorial_pos _)
/-
**Nat.doubleFactorial_add_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：doubleFactorial_add_two (n : Nat) : (n + 2)‼ = (n + 2) * n‼
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem doubleFactorial_add_two (n : ℕ) : (n + 2)‼ = (n + 2) * n‼ :=
  rfl
/-
**Nat.doubleFactorial_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：doubleFactorial_add_one (n : Nat) : (n + 1)‼ = (n + 1) * (n - 1)‼
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem doubleFactorial_add_one (n : ℕ) : (n + 1)‼ = (n + 1) * (n - 1)‼ := by cases n <;> rfl
/-
**Nat.factorial_eq_mul_doubleFactorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), (n + 1).factorial = (n + 1).doubleFactorial * n.doubleFactorial
参数：n : ℕ；n + 1；n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem factorial_eq_mul_doubleFactorial : ∀ n : ℕ, (n + 1)! = (n + 1)‼ * n‼
  | 0 => rfl
  | k + 1 => by
    rw [doubleFactorial_add_two, factorial, factorial_eq_mul_doubleFactorial _, mul_comm _ k‼,
      mul_assoc]
/-
**Nat.doubleFactorial_le_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), n.doubleFactorial ≤ n.factorial
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorial_eq_mul_doubleFactorial`：∀ (n : ℕ), (n + 1).factorial = (n 
+ 1).doubleFactorial * n.doubleFactorial
· 使用定理 `Nat.le_mul_of_pos_right`：∀ {m : ℕ} (n : ℕ), 0 < m → n ≤ n * m
· 使用定理 `Nat.doubleFactorial_pos`：∀ (n : ℕ), 0 < n.doubleFactorial
-/
lemma doubleFactorial_le_factorial : ∀ n, n‼ ≤ n !
  | 0 => le_rfl
  | n + 1 => by
    rw [factorial_eq_mul_doubleFactorial]; exact Nat.le_mul_of_pos_right _ n.doubleFactorial_pos
/-
**Nat.doubleFactorial_two_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), (2 * n).doubleFactorial = 2 ^ n * n.factorial
参数：n : ℕ；2 * n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem doubleFactorial_two_mul : ∀ n : ℕ, (2 * n)‼ = 2 ^ n * n !
  | 0 => rfl
  | n + 1 => by
    rw [mul_add, mul_one, doubleFactorial_add_two, factorial, pow_succ, doubleFactorial_two_mul _,
      succ_eq_add_one]
    ring
/-
**Nat.doubleFactorial_eq_prod_even** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), (2 * n).doubleFactorial = ∏ i ∈ Finset.range n, 2 * (i + 1)
参数：n : ℕ；2 * n；i + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem doubleFactorial_eq_prod_even : ∀ n : ℕ, (2 * n)‼ = ∏ i ∈ Finset.range n, 2 * (i + 1)
  | 0 => rfl
  | n + 1 => by
    rw [Finset.prod_range_succ, ← doubleFactorial_eq_prod_even _, mul_comm (2 * n)‼,
      (by ring : 2 * (n + 1) = 2 * n + 2)]
    rfl
/-
**Nat.doubleFactorial_eq_prod_odd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), (2 * n + 1).doubleFactorial = ∏ i ∈ Finset.range n, (2 * (i + 1
) + 1)
参数：n : ℕ；2 * n + 1；2 * (i + 1) + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem doubleFactorial_eq_prod_odd :
    ∀ n : ℕ, (2 * n + 1)‼ = ∏ i ∈ Finset.range n, (2 * (i + 1) + 1)
  | 0 => rfl
  | n + 1 => by
    rw [Finset.prod_range_succ, ← doubleFactorial_eq_prod_odd _, mul_comm (2 * n + 1)‼,
      (by ring : 2 * (n + 1) + 1 = 2 * n + 1 + 2)]
    rfl

end Nat

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- Extension for `Nat.doubleFactorial`. -/
@[positivity Nat.doubleFactorial _]
meta def evalDoubleFactorial : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Nat.doubleFactorial $n) =>
    assumeInstancesCommute
    return .positive q(Nat.doubleFactorial_pos $n)
  | _, _ => throwError "not Nat.doubleFactorial"

/-
**Mathlib.Meta.Positivity.** 是 Mathlib 中的一个示例，位于命名空间 `Mathlib.Meta.Positivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (n : ℕ) : 0 < n‼ := by positivity

end Mathlib.Meta.Positivity

