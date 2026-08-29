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

/--
theorem `exists_infinite_primes` / 定理 `exists_infinite_primes`

English:
theorem exists_infinite_primes
  given: (n : Nat)
  statement: exists p, n <= p ∧ Prime p
  proof: let p := minFac (n ! + 1)
have f1 : n ! + 1 != 1 := ne_of_gt succ_lt_succ factorial_pos _
  have pp : Prime p := minFac_prime f1
  have np : n <= p :=
    le_of_not_ge fun h =>
      have h₁ : p ∣ n ! := dvd_factorial (minFac_pos _) h
      have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2 (minFac_dvd

中文:
定理 存在_infinite_primes
  条件: (n : 自然数)
  结论: 存在 p, n <= p ∧ 素 p
  证明: let p := minFac (n ! + 1)
have f1 : n ! + 1 != 1 := ne_of_gt succ_lt_succ factorial_pos _
  have pp : Prime p := minFac_prime f1
  have np : n <= p :=
    le_of_not_ge fun h =>
      have h₁ : p ∣ n ! := dvd_factorial (minFac_pos _) h
      have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2 (minFac_dvd

Depends on / 依赖: Nat.dvd_add_iff_right, dvd_add_iff_right, dvd_factorial, factorial_pos, le_of_not_ge, minFac, minFac_dvd, minFac_pos, minFac_prime, ne_of_gt, not_dvd_one, pp.not_dvd_one, succ_lt_succ
-/
theorem exists_infinite_primes (n : Nat) : exists p, n <= p ∧ Prime p :=
  let p := minFac (n ! + 1)
have f1 : n ! + 1 != 1 := ne_of_gt succ_lt_succ factorial_pos _
  have pp : Prime p := minFac_prime f1
  have np : n <= p :=
    le_of_not_ge fun h =>
      have h₁ : p ∣ n ! := dvd_factorial (minFac_pos _) h
      have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2 (minFac_dvd _)
      pp.not_dvd_one h₂
  ⟨p, np, pp⟩

/--
theorem `not_bddAbove_setOfPred_prime` / 定理 `not_bddAbove_setOfPred_prime`

English:
theorem not_bddAbove_setOfPred_prime
  statement: ¬BddAbove { p | Prime p }
  proof: by
  rw [not_bddAbove_iff]
  intro n
  obtain ⟨p, hi, hp⟩ := exists_infinite_primes n.succ
  exact ⟨p, hp, hi⟩

@[deprecated (since := "2026-07-09")] alias not_bddAbove_setOf_prime := not_bddAbove_setOfPred_prime

中文:
定理 not_bddAbove_setOfPred_prime
  结论: ¬BddAbove { p | 素 p }
  证明: by
  rw [not_bddAbove_iff]
  intro n
  obtain ⟨p, hi, hp⟩ := exists_infinite_primes n.succ
  exact ⟨p, hp, hi⟩

@[deprecated (since := "2026-07-09")] alias not_bddAbove_setOf_prime := not_bddAbove_setOfPred_prime

Depends on / 依赖: exists_infinite_primes, n.succ, not_bddAbove_iff
-/
theorem not_bddAbove_setOfPred_prime : ¬BddAbove { p | Prime p } := by
  rw [not_bddAbove_iff]
  intro n
  obtain ⟨p, hi, hp⟩ := exists_infinite_primes n.succ
  exact ⟨p, hp, hi⟩

@[deprecated (since := "2026-07-09")] alias not_bddAbove_setOf_prime := not_bddAbove_setOfPred_prime

end Infinite

end Nat
