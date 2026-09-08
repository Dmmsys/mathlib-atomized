/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Bounds.Basic

/-!
## Notable Theorems

- `Nat.exists_infinite_primes`: Euclid's theorem that there exist infinitely many prime numbers.
  This also appears as `Nat.not_bddAbove_setOfPred_prime` and `Nat.infinite_setOfPred_prime`
  (the latter in `Data.Nat.PrimeFin`).

-/

public section

open Bool Subtype

open Nat

namespace Nat

section Infinite

/-- Euclid's theorem on the **infinitude of primes**.
Here given in the form: for every `n`, there exists a prime number `p ≥ n`. -/
/-
**Nat.exists_infinite_primes** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exists_infinite_primes (n : Nat) : exists p, n <= p ∧ Prime p
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
· 使用定理 `Nat.dvd_factorial`：∀ {m n : ℕ}, 0 < m → m ≤ n → m ∣ n.factorial
· 使用定理 `Nat.minFac_pos`：minFac_pos (n : Nat) : 0 < minFac n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.dvd_add_iff_right`：∀ {k m n : ℕ}, k ∣ m → (k ∣ n ↔ k ∣ m + n)
· 使用定理 `Nat.minFac_dvd`：minFac_dvd (n : Nat) : minFac n ∣ n
· 使用定理 `Nat.Prime.not_dvd_one`：∀ {p : ℕ}, Nat.Prime p → ¬p ∣ 1

--- 原说明 ---
Euclid's theorem on the **infinitude of primes**.
Here given in the form: for every `n`, there exists a prime number `p ≥ n`.
-/
theorem exists_infinite_primes (n : ℕ) : ∃ p, n ≤ p ∧ Prime p :=
  let p := minFac (n ! + 1)
  have f1 : n ! + 1 ≠ 1 := ne_of_gt <| succ_lt_succ <| factorial_pos _
  have pp : Prime p := minFac_prime f1
  have np : n ≤ p :=
    le_of_not_ge fun h =>
      have h₁ : p ∣ n ! := dvd_factorial (minFac_pos _) h
      have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2 (minFac_dvd _)
      pp.not_dvd_one h₂
  ⟨p, np, pp⟩

/-- A version of `Nat.exists_infinite_primes` using the `BddAbove` predicate. -/
/-
**Nat.not_bddAbove_setOfPred_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：not_bddAbove_setOfPred_prime : ¬BddAbove { p | Prime p }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_bddAbove_iff`：not_bddAbove_iff {α : Type*} [LinearOrder α] {s : Set 
α} : ¬BddAbove s ↔ forall x, exists y in s, x < y
· 使用定理 `Nat.exists_infinite_primes`：exists_infinite_primes (n : Nat) : exists p,
 n <= p ∧ Prime p

--- 原说明 ---
A version of `Nat.exists_infinite_primes` using the `BddAbove` predicate.
-/
theorem not_bddAbove_setOfPred_prime : ¬BddAbove { p | Prime p } := by
  rw [not_bddAbove_iff]
  intro n
  obtain ⟨p, hi, hp⟩ := exists_infinite_primes n.succ
  exact ⟨p, hp, hi⟩

@[deprecated (since := "2026-07-09")] alias not_bddAbove_setOf_prime := not_bddAbove_setOfPred_prime

end Infinite

end Nat

