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
/--
Definition of `doubleFactorial` / `doubleFactorial` 的定义

English:
definition doubleFactorial
  signature: : Nat -> Nat

中文:
定义 doubleFactorial
  签名: : 自然数 -> 自然数
-/
def doubleFactorial : Nat -> Nat
  | 0 => 1
  | 1 => 1
  | k + 2 => (k + 2) * doubleFactorial k

-- This notation is `\!!` not two !'s
@[inherit_doc] scoped notation:10000 n "‼" => Nat.doubleFactorial n

/--
lemma `doubleFactorial_pos` / 引理 `doubleFactorial_pos`

English:
lemma doubleFactorial_pos
  statement: forall n, 0 < n‼

中文:
引理 doubleFactorial_pos
  结论: 对任意 n, 0 < n‼
-/
lemma doubleFactorial_pos : forall n, 0 < n‼
  | 0 | 1 => zero_lt_one
  | _n + 2 => mul_pos (succ_pos _) (doubleFactorial_pos _)

/--
theorem `doubleFactorial_add_two` / 定理 `doubleFactorial_add_two`

English:
theorem doubleFactorial_add_two
  given: (n : Nat)
  statement: (n + 2)‼ = (n + 2) * n‼
  proof: rfl

中文:
定理 doubleFactorial_add_two
  条件: (n : 自然数)
  结论: (n + 2)‼ = (n + 2) * n‼
  证明: rfl
-/
theorem doubleFactorial_add_two (n : Nat) : (n + 2)‼ = (n + 2) * n‼ :=
  rfl

/--
theorem `doubleFactorial_add_one` / 定理 `doubleFactorial_add_one`

English:
theorem doubleFactorial_add_one
  given: (n : Nat)
  statement: (n + 1)‼ = (n + 1) * (n - 1)‼
  proof: by cases n <;> rfl

中文:
定理 doubleFactorial_add_one
  条件: (n : 自然数)
  结论: (n + 1)‼ = (n + 1) * (n - 1)‼
  证明: by cases n <;> rfl
-/
theorem doubleFactorial_add_one (n : Nat) : (n + 1)‼ = (n + 1) * (n - 1)‼ := by cases n <;> rfl

/--
theorem `factorial_eq_mul_doubleFactorial` / 定理 `factorial_eq_mul_doubleFactorial`

English:
theorem factorial_eq_mul_doubleFactorial
  statement: forall n : Nat, (n + 1)! = (n + 1)‼ * n‼

中文:
定理 factorial_eq_mul_doubleFactorial
  结论: 对任意 n : 自然数, (n + 1)! = (n + 1)‼ * n‼
-/
theorem factorial_eq_mul_doubleFactorial : forall n : Nat, (n + 1)! = (n + 1)‼ * n‼
  | 0 => rfl
  | k + 1 => by
    rw [doubleFactorial_add_two]; rw [factorial]; rw [factorial_eq_mul_doubleFactorial _]; rw [mul_comm _ k‼]; rw [mul_assoc]

/--
lemma `doubleFactorial_le_factorial` / 引理 `doubleFactorial_le_factorial`

English:
lemma doubleFactorial_le_factorial
  statement: forall n, n‼ <= n !

中文:
引理 doubleFactorial_le_factorial
  结论: 对任意 n, n‼ <= n !
-/
lemma doubleFactorial_le_factorial : forall n, n‼ <= n !
  | 0 => le_rfl
  | n + 1 => by
    rw [factorial_eq_mul_doubleFactorial]; exact Nat.le_mul_of_pos_right _ n.doubleFactorial_pos

/--
theorem `doubleFactorial_two_mul` / 定理 `doubleFactorial_two_mul`

English:
theorem doubleFactorial_two_mul
  statement: forall n : Nat, (2 * n)‼ = 2 ^ n * n !

中文:
定理 doubleFactorial_two_mul
  结论: 对任意 n : 自然数, (2 * n)‼ = 2 ^ n * n !
-/
theorem doubleFactorial_two_mul : forall n : Nat, (2 * n)‼ = 2 ^ n * n !
  | 0 => rfl
  | n + 1 => by
    rw [mul_add]; rw [mul_one]; rw [doubleFactorial_add_two]; rw [factorial]; rw [pow_succ]; rw [doubleFactorial_two_mul _]; rw [succ_eq_add_one]
    ring

/--
theorem `doubleFactorial_eq_prod_even` / 定理 `doubleFactorial_eq_prod_even`

English:
theorem doubleFactorial_eq_prod_even
  statement: forall n : Nat, (2 * n)‼ = ∏ i in Finset.range n, 2 * (i + 1)

中文:
定理 doubleFactorial_eq_prod_even
  结论: 对任意 n : 自然数, (2 * n)‼ = ∏ i in 有限集.range n, 2 * (i + 1)
-/
theorem doubleFactorial_eq_prod_even : forall n : Nat, (2 * n)‼ = ∏ i in Finset.range n, 2 * (i + 1)
  | 0 => rfl
  | n + 1 => by
    rw [Finset.prod_range_succ]; rw [← doubleFactorial_eq_prod_even _]; rw [mul_comm (2 * n)‼]; rw [(by ring : 2 * (n + 1) = 2 * n + 2)]
    rfl

/--
theorem `doubleFactorial_eq_prod_odd` / 定理 `doubleFactorial_eq_prod_odd`

English:
theorem doubleFactorial_eq_prod_odd

中文:
定理 doubleFactorial_eq_prod_odd
-/
theorem doubleFactorial_eq_prod_odd :
    forall n : Nat, (2 * n + 1)‼ = ∏ i in Finset.range n, (2 * (i + 1) + 1)
  | 0 => rfl
  | n + 1 => by
    rw [Finset.prod_range_succ]; rw [← doubleFactorial_eq_prod_odd _]; rw [mul_comm (2 * n + 1)‼]; rw [(by ring : 2 * (n + 1) + 1 = 2 * n + 1 + 2)]
    rfl

end Nat

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- Extension for `Nat.doubleFactorial`. -/
@[positivity Nat.doubleFactorial _]
meta def evalDoubleFactorial : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Nat), ~q(Nat.doubleFactorial $n) =>
    assumeInstancesCommute
    return .positive q(Nat.doubleFactorial_pos $n)
  | _, _ => throwError "not Nat.doubleFactorial"

example (n : Nat) : 0 < n‼ := by positivity

end Mathlib.Meta.Positivity
