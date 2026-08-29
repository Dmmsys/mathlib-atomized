/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Almost prime numbers

This file defines `Nat.IsAlmostPrime k n`, the predicate that `n` has exactly `k`
prime factors counted with multiplicity. We also define `Nat.IsAtMostAlmostPrime`,
the corresponding predicate with at most `k` prime factors, and `Nat.IsSemiprime`,
the special case of `2`-almost-prime numbers.

Both definitions use the arithmetic function `ArithmeticFunction.cardFactors`, written `Ω`.

The terminology follows the standard definition of an
[almost prime](https://en.wikipedia.org/wiki/Almost_prime).

## Main statements

* `Nat.IsAlmostPrime.mul`: the product of a `k`-almost-prime number and an
  `l`-almost-prime number is `(k + l)`-almost-prime.
* `Nat.IsAtMostAlmostPrime.mul`: the analogous statement for at most `k` prime factors.

-/

@[expose] public section

open scoped ArithmeticFunction.Omega

namespace Nat

/--
Definition of `IsAlmostPrime` / `IsAlmostPrime` 的定义

English:
definition IsAlmostPrime
  signature: (k n : Nat)
  body: n != 0 ∧ Ω n = k

中文:
定义 IsAlmostPrime
  签名: (k n : 自然数)
  定义体: n != 0 ∧ Ω n = k
-/
def IsAlmostPrime (k n : Nat) : Prop :=
  n != 0 ∧ Ω n = k

/--
Definition of `IsAtMostAlmostPrime` / `IsAtMostAlmostPrime` 的定义

English:
definition IsAtMostAlmostPrime
  signature: (k n : Nat)
  body: n != 0 ∧ Ω n <= k

中文:
定义 IsAtMostAlmostPrime
  签名: (k n : 自然数)
  定义体: n != 0 ∧ Ω n <= k
-/
def IsAtMostAlmostPrime (k n : Nat) : Prop :=
  n != 0 ∧ Ω n <= k

/--
Definition of `IsSemiprime` / `IsSemiprime` 的定义

English:
abbreviation IsSemiprime
  signature: (n : Nat)
  body: IsAlmostPrime 2 n

中文:
缩写 IsSemiprime
  签名: (n : 自然数)
  定义体: IsAlmostPrime 2 n

Depends on / 依赖: IsAlmostPrime
-/
abbrev IsSemiprime (n : Nat) : Prop :=
  IsAlmostPrime 2 n

variable {k l m n p q : Nat}

@[simp]
/--
theorem `isAlmostPrime_zero_iff` / 定理 `isAlmostPrime_zero_iff`

English:
theorem isAlmostPrime_zero_iff
  statement: IsAlmostPrime 0 n ↔ n = 1
  proof: by
  rw [IsAlmostPrime]; rw [ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one]
  exact ⟨fun h => h.2.resolve_left h.1, fun h => by simp [h]⟩

@[simp]

中文:
定理 isAlmostPrime_zero_iff
  结论: IsAlmostPrime 0 n ↔ n = 1
  证明: by
  rw [IsAlmostPrime]; rw [ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one]
  exact ⟨fun h => h.2.resolve_left h.1, fun h => by simp [h]⟩

@[simp]

Depends on / 依赖: ArithmeticFunction, ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one, IsAlmostPrime, cardFactors_eq_zero_iff_eq_zero_or_one, resolve_left
-/
theorem isAlmostPrime_zero_iff : IsAlmostPrime 0 n ↔ n = 1 := by
  rw [IsAlmostPrime]; rw [ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one]
  exact ⟨fun h => h.2.resolve_left h.1, fun h => by simp [h]⟩

@[simp]
/--
theorem `isAlmostPrime_one_iff` / 定理 `isAlmostPrime_one_iff`

English:
theorem isAlmostPrime_one_iff
  statement: IsAlmostPrime 1 n ↔ n.Prime
  proof: by
  constructor
  · exact fun h => ArithmeticFunction.cardFactors_eq_one_iff_prime.mp h.2
  · exact fun h => ⟨h.ne_zero, ArithmeticFunction.cardFactors_eq_one_iff_prime.mpr h⟩

中文:
定理 isAlmostPrime_one_iff
  结论: IsAlmostPrime 1 n ↔ n.Prime
  证明: by
  constructor
  · exact fun h => ArithmeticFunction.cardFactors_eq_one_iff_prime.mp h.2
  · exact fun h => ⟨h.ne_zero, ArithmeticFunction.cardFactors_eq_one_iff_prime.mpr h⟩

Depends on / 依赖: ArithmeticFunction, ArithmeticFunction.cardFactors_eq_one_iff_prime.mp, ArithmeticFunction.cardFactors_eq_one_iff_prime.mpr, cardFactors_eq_one_iff_prime, h.ne_zero, ne_zero
-/
theorem isAlmostPrime_one_iff : IsAlmostPrime 1 n ↔ n.Prime := by
  constructor
  · exact fun h => ArithmeticFunction.cardFactors_eq_one_iff_prime.mp h.2
  · exact fun h => ⟨h.ne_zero, ArithmeticFunction.cardFactors_eq_one_iff_prime.mpr h⟩

/--
theorem `Prime.isAlmostPrime_one` / 定理 `Prime.isAlmostPrime_one`

English:
theorem Prime.isAlmostPrime_one
  given: (hp : p.Prime)
  statement: IsAlmostPrime 1 p
  proof: by
  simpa using isAlmostPrime_one_iff.mpr hp

中文:
定理 Prime.isAlmostPrime_one
  条件: (hp : p.Prime)
  结论: IsAlmostPrime 1 p
  证明: by
  simpa using isAlmostPrime_one_iff.mpr hp

Depends on / 依赖: isAlmostPrime_one_iff, isAlmostPrime_one_iff.mpr
-/
theorem Prime.isAlmostPrime_one (hp : p.Prime) : IsAlmostPrime 1 p := by
  simpa using isAlmostPrime_one_iff.mpr hp

/--
theorem `IsAlmostPrime.mul` / 定理 `IsAlmostPrime.mul`

English:
theorem IsAlmostPrime.mul
  given: (hm : IsAlmostPrime k m) (hn : IsAlmostPrime l n)
  proof: by
  refine ⟨mul_ne_zero hm.1 hn.1, ?_⟩
  rw [ArithmeticFunction.cardFactors_mul hm.1 hn.1]; rw [hm.2]; rw [hn.2]

中文:
定理 IsAlmostPrime.mul
  条件: (hm : IsAlmostPrime k m) (hn : IsAlmostPrime l n)
  证明: by
  refine ⟨mul_ne_zero hm.1 hn.1, ?_⟩
  rw [ArithmeticFunction.cardFactors_mul hm.1 hn.1]; rw [hm.2]; rw [hn.2]

Depends on / 依赖: ArithmeticFunction, ArithmeticFunction.cardFactors_mul, cardFactors_mul, mul_ne_zero
-/
theorem IsAlmostPrime.mul (hm : IsAlmostPrime k m) (hn : IsAlmostPrime l n) :
    IsAlmostPrime (k + l) (m * n) := by
  refine ⟨mul_ne_zero hm.1 hn.1, ?_⟩
  rw [ArithmeticFunction.cardFactors_mul hm.1 hn.1]; rw [hm.2]; rw [hn.2]

/--
theorem `IsAtMostAlmostPrime.mul` / 定理 `IsAtMostAlmostPrime.mul`

English:
theorem IsAtMostAlmostPrime.mul
  given: (hm : IsAtMostAlmostPrime k m) (hn : IsAtMostAlmostPrime l n)
  proof: by
  refine ⟨mul_ne_zero hm.1 hn.1, ?_⟩
  rw [ArithmeticFunction.cardFactors_mul hm.1 hn.1]
  exact add_le_add hm.2 hn.2

中文:
定理 IsAtMostAlmostPrime.mul
  条件: (hm : IsAtMostAlmostPrime k m) (hn : IsAtMostAlmostPrime l n)
  证明: by
  refine ⟨mul_ne_zero hm.1 hn.1, ?_⟩
  rw [ArithmeticFunction.cardFactors_mul hm.1 hn.1]
  exact add_le_add hm.2 hn.2

Depends on / 依赖: ArithmeticFunction, ArithmeticFunction.cardFactors_mul, add_le_add, cardFactors_mul, mul_ne_zero
-/
theorem IsAtMostAlmostPrime.mul (hm : IsAtMostAlmostPrime k m) (hn : IsAtMostAlmostPrime l n) :
    IsAtMostAlmostPrime (k + l) (m * n) := by
  refine ⟨mul_ne_zero hm.1 hn.1, ?_⟩
  rw [ArithmeticFunction.cardFactors_mul hm.1 hn.1]
  exact add_le_add hm.2 hn.2

/--
theorem `IsAlmostPrime.isAtMost` / 定理 `IsAlmostPrime.isAtMost`

English:
theorem IsAlmostPrime.isAtMost
  given: (hn : IsAlmostPrime k n) (hkl : k <= l)
  proof: ⟨hn.1, hn.2 ▸ hkl⟩

中文:
定理 IsAlmostPrime.isAtMost
  条件: (hn : IsAlmostPrime k n) (hkl : k <= l)
  证明: ⟨hn.1, hn.2 ▸ hkl⟩
-/
theorem IsAlmostPrime.isAtMost (hn : IsAlmostPrime k n) (hkl : k <= l) :
    IsAtMostAlmostPrime l n :=
  ⟨hn.1, hn.2 ▸ hkl⟩

/--
theorem `Prime.mul_isAlmostPrime_two` / 定理 `Prime.mul_isAlmostPrime_two`

English:
theorem Prime.mul_isAlmostPrime_two
  given: (hp : p.Prime) (hq : q.Prime)
  proof: by
  simpa using hp.isAlmostPrime_one.mul hq.isAlmostPrime_one

中文:
定理 Prime.mul_isAlmostPrime_two
  条件: (hp : p.Prime) (hq : q.Prime)
  证明: by
  simpa using hp.isAlmostPrime_one.mul hq.isAlmostPrime_one

Depends on / 依赖: hp.isAlmostPrime_one.mul, hq.isAlmostPrime_one, isAlmostPrime_one
-/
theorem Prime.mul_isAlmostPrime_two (hp : p.Prime) (hq : q.Prime) :
    IsAlmostPrime 2 (p * q) := by
  simpa using hp.isAlmostPrime_one.mul hq.isAlmostPrime_one

/--
theorem `Prime.sq_isAlmostPrime_two` / 定理 `Prime.sq_isAlmostPrime_two`

English:
theorem Prime.sq_isAlmostPrime_two
  given: (hp : p.Prime)
  statement: IsAlmostPrime 2 (p ^ 2)
  proof: by
  simpa [pow_two] using hp.mul_isAlmostPrime_two hp

中文:
定理 Prime.sq_isAlmostPrime_two
  条件: (hp : p.Prime)
  结论: IsAlmostPrime 2 (p ^ 2)
  证明: by
  simpa [pow_two] using hp.mul_isAlmostPrime_two hp

Depends on / 依赖: hp.mul_isAlmostPrime_two, mul_isAlmostPrime_two, pow_two
-/
theorem Prime.sq_isAlmostPrime_two (hp : p.Prime) : IsAlmostPrime 2 (p ^ 2) := by
  simpa [pow_two] using hp.mul_isAlmostPrime_two hp

end Nat
