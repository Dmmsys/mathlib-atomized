/-
Copyright (c) 2024 Colin Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Jones
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum

/-!
# Factorisation properties of natural numbers

This file defines abundant, pseudoperfect, deficient, and weird numbers and formalizes their
relations with prime and perfect numbers.

## Main Definitions

* `Nat.Abundant`: a natural number `n` is _abundant_ if the sum of its proper divisors is greater
  than `n`
* `Nat.Pseudoperfect`: a natural number `n` is _pseudoperfect_ if the sum of a subset of its proper
  divisors equals `n`
* `Nat.Deficient`: a natural number `n` is _deficient_ if the sum of its proper divisors is less
  than `n`
* `Nat.Weird`: a natural number is _weird_ if it is abundant but not pseudoperfect

## Main Results

* `Nat.deficient_or_perfect_or_abundant`: A positive natural number is either deficient,
  perfect, or abundant.
* `Nat.Prime.deficient`: All prime natural numbers are deficient.
* `Nat.infinite_deficient`: There are infinitely many deficient numbers.
* `Nat.Prime.deficient_pow`: Any natural number power of a prime is deficient.

## Implementation Notes
* Zero is not included in any of the definitions and these definitions only apply to natural
  numbers greater than zero.

## References
* [R. W. Prielipp, *PERFECT NUMBERS, ABUNDANT NUMBERS, AND DEFICIENT NUMBERS*][Prielipp1970]

## Tags

abundant, deficient, weird, pseudoperfect
-/

@[expose] public section

open Finset

namespace Nat

variable {n m p : Nat}

/--
Definition of `Abundant` / `Abundant` 的定义

English:
definition Abundant
  signature: (n : Nat)
  body: n < ∑ i in properDivisors n, i
deriving Decidable

中文:
定义 Abundant
  签名: (n : 自然数)
  定义体: n < ∑ i in properDivisors n, i
deriving Decidable

Depends on / 依赖: properDivisors
-/
def Abundant (n : Nat) : Prop := n < ∑ i in properDivisors n, i
deriving Decidable

/--
Definition of `Deficient` / `Deficient` 的定义

English:
definition Deficient
  signature: (n : Nat)
  body: ∑ i in properDivisors n, i < n
deriving Decidable

中文:
定义 Deficient
  签名: (n : 自然数)
  定义体: ∑ i in properDivisors n, i < n
deriving Decidable

Depends on / 依赖: properDivisors
-/
def Deficient (n : Nat) : Prop := ∑ i in properDivisors n, i < n
deriving Decidable

/--
Definition of `Pseudoperfect` / `Pseudoperfect` 的定义

English:
definition Pseudoperfect
  signature: (n : Nat)
  body: 0 < n ∧ exists s subseteq properDivisors n, ∑ i in s, i = n
deriving Decidable

中文:
定义 Pseudoperfect
  签名: (n : 自然数)
  定义体: 0 < n ∧ exists s subseteq properDivisors n, ∑ i in s, i = n
deriving Decidable

Depends on / 依赖: properDivisors, subseteq
-/
def Pseudoperfect (n : Nat) : Prop :=
  0 < n ∧ exists s subseteq properDivisors n, ∑ i in s, i = n
deriving Decidable

/--
Definition of `Weird` / `Weird` 的定义

English:
definition Weird
  signature: (n : Nat)
  body: Abundant n ∧ ¬ Pseudoperfect n
deriving Decidable

中文:
定义 Weird
  签名: (n : 自然数)
  定义体: Abundant n ∧ ¬ Pseudoperfect n
deriving Decidable

Depends on / 依赖: Abundant, Pseudoperfect
-/
def Weird (n : Nat) : Prop := Abundant n ∧ ¬ Pseudoperfect n
deriving Decidable

/--
Definition of `abundancyIndex` / `abundancyIndex` 的定义

English:
definition abundancyIndex
  signature: (n : Nat)
  body: (∑ i in n.divisors, i) / (n : Rat)

中文:
定义 abundancyIndex
  签名: (n : 自然数)
  定义体: (∑ i in n.divisors, i) / (n : Rat)

Depends on / 依赖: divisors, n.divisors
-/
def abundancyIndex (n : Nat) : Rat := (∑ i in n.divisors, i) / (n : Rat)

/--
theorem `not_pseudoperfect_iff_forall` / 定理 `not_pseudoperfect_iff_forall`

English:
theorem not_pseudoperfect_iff_forall
  proof: by
  grind [Pseudoperfect]

中文:
定理 not_pseudoperfect_iff_forall
  证明: by
  grind [Pseudoperfect]

Depends on / 依赖: Pseudoperfect
-/
theorem not_pseudoperfect_iff_forall :
    ¬ Pseudoperfect n ↔ n = 0 ∨ forall s subseteq properDivisors n, ∑ i in s, i != n := by
  grind [Pseudoperfect]

/--
theorem `not_deficient_zero` / 定理 `not_deficient_zero`

English:
theorem not_deficient_zero
  statement: ¬ Deficient 0
  proof: by
  decide

中文:
定理 not_deficient_zero
  结论: ¬ Deficient 0
  证明: by
  decide
-/
theorem not_deficient_zero : ¬ Deficient 0 := by
  decide

/--
theorem `deficient_one` / 定理 `deficient_one`

English:
theorem deficient_one
  statement: Deficient 1
  proof: by
  decide

中文:
定理 deficient_one
  结论: Deficient 1
  证明: by
  decide
-/
theorem deficient_one : Deficient 1 := by
  decide

/--
theorem `deficient_two` / 定理 `deficient_two`

English:
theorem deficient_two
  statement: Deficient 2
  proof: by
  decide

中文:
定理 deficient_two
  结论: Deficient 2
  证明: by
  decide
-/
theorem deficient_two : Deficient 2 := by
  decide

/--
theorem `deficient_three` / 定理 `deficient_three`

English:
theorem deficient_three
  statement: Deficient 3
  proof: by
  decide

中文:
定理 deficient_three
  结论: Deficient 3
  证明: by
  decide
-/
theorem deficient_three : Deficient 3 := by
  decide

/--
theorem `not_abundant_zero` / 定理 `not_abundant_zero`

English:
theorem not_abundant_zero
  statement: ¬ Abundant 0
  proof: by
  decide

中文:
定理 not_abundant_zero
  结论: ¬ Abundant 0
  证明: by
  decide
-/
theorem not_abundant_zero : ¬ Abundant 0 := by
  decide

/--
theorem `abundant_twelve` / 定理 `abundant_twelve`

English:
theorem abundant_twelve
  statement: Abundant 12
  proof: by
  decide

中文:
定理 abundant_twelve
  结论: Abundant 12
  证明: by
  decide
-/
theorem abundant_twelve : Abundant 12 := by
  decide

/--
theorem `not_weird_zero` / 定理 `not_weird_zero`

English:
theorem not_weird_zero
  statement: ¬ Weird 0
  proof: by
  decide

中文:
定理 not_weird_zero
  结论: ¬ Weird 0
  证明: by
  decide
-/
theorem not_weird_zero : ¬ Weird 0 := by
  decide

/--
theorem `weird_seventy` / 定理 `weird_seventy`

English:
theorem weird_seventy
  statement: Weird 70
  proof: by
  decide +kernel

中文:
定理 weird_seventy
  结论: Weird 70
  证明: by
  decide +kernel

Depends on / 依赖: kernel
-/
theorem weird_seventy : Weird 70 := by
  decide +kernel

/--
lemma `Deficient.pos` / 引理 `Deficient.pos`

English:
lemma Deficient.pos
  given: (h : Deficient n)
  statement: 0 < n
  proof: by
  grind only [not_deficient_zero]

中文:
引理 Deficient.pos
  条件: (h : Deficient n)
  结论: 0 < n
  证明: by
  grind only [not_deficient_zero]

Depends on / 依赖: not_deficient_zero
-/
lemma Deficient.pos (h : Deficient n) : 0 < n := by
  grind only [not_deficient_zero]

/--
lemma `Abundant.pos` / 引理 `Abundant.pos`

English:
lemma Abundant.pos
  given: (h : Abundant n)
  statement: 0 < n
  proof: by
  grind only [not_abundant_zero]

中文:
引理 Abundant.pos
  条件: (h : Abundant n)
  结论: 0 < n
  证明: by
  grind only [not_abundant_zero]

Depends on / 依赖: not_abundant_zero
-/
lemma Abundant.pos (h : Abundant n) : 0 < n := by
  grind only [not_abundant_zero]

/--
lemma `Weird.pos` / 引理 `Weird.pos`

English:
lemma Weird.pos
  given: (h : Weird n)
  statement: 0 < n
  proof: by
  grind only [not_weird_zero]

中文:
引理 Weird.pos
  条件: (h : Weird n)
  结论: 0 < n
  证明: by
  grind only [not_weird_zero]

Depends on / 依赖: not_weird_zero
-/
lemma Weird.pos (h : Weird n) : 0 < n := by
  grind only [not_weird_zero]

/--
lemma `deficient_iff_not_abundant_and_not_perfect` / 引理 `deficient_iff_not_abundant_and_not_perfect`

English:
lemma deficient_iff_not_abundant_and_not_perfect
  given: (hn : n != 0)
  proof: by
  grind [Perfect, Abundant, Deficient]

中文:
引理 deficient_iff_not_abundant_and_not_perfect
  条件: (hn : n != 0)
  证明: by
  grind [Perfect, Abundant, Deficient]

Depends on / 依赖: Abundant, Deficient, Perfect
-/
lemma deficient_iff_not_abundant_and_not_perfect (hn : n != 0) :
    Deficient n ↔ ¬ Abundant n ∧ ¬ Perfect n := by
  grind [Perfect, Abundant, Deficient]

/--
lemma `perfect_iff_not_abundant_and_not_deficient` / 引理 `perfect_iff_not_abundant_and_not_deficient`

English:
lemma perfect_iff_not_abundant_and_not_deficient
  given: (hn : 0 != n)
  proof: by
  grind [Perfect, Abundant, Deficient]

中文:
引理 perfect_iff_not_abundant_and_not_deficient
  条件: (hn : 0 != n)
  证明: by
  grind [Perfect, Abundant, Deficient]

Depends on / 依赖: Abundant, Deficient, Perfect
-/
lemma perfect_iff_not_abundant_and_not_deficient (hn : 0 != n) :
    Perfect n ↔ ¬ Abundant n ∧ ¬ Deficient n := by
  grind [Perfect, Abundant, Deficient]

/--
lemma `abundant_iff_not_perfect_and_not_deficient` / 引理 `abundant_iff_not_perfect_and_not_deficient`

English:
lemma abundant_iff_not_perfect_and_not_deficient
  given: (hn : 0 != n)
  proof: by
  grind [Perfect, Abundant, Deficient]

中文:
引理 abundant_iff_not_perfect_and_not_deficient
  条件: (hn : 0 != n)
  证明: by
  grind [Perfect, Abundant, Deficient]

Depends on / 依赖: Abundant, Deficient, Perfect
-/
lemma abundant_iff_not_perfect_and_not_deficient (hn : 0 != n) :
    Abundant n ↔ ¬ Perfect n ∧ ¬ Deficient n := by
  grind [Perfect, Abundant, Deficient]

/--
theorem `deficient_or_perfect_or_abundant` / 定理 `deficient_or_perfect_or_abundant`

English:
theorem deficient_or_perfect_or_abundant
  given: (hn : 0 != n)
  proof: by
  grind [Perfect, Abundant, Deficient]

中文:
定理 deficient_or_perfect_or_abundant
  条件: (hn : 0 != n)
  证明: by
  grind [Perfect, Abundant, Deficient]

Depends on / 依赖: Abundant, Deficient, Perfect
-/
theorem deficient_or_perfect_or_abundant (hn : 0 != n) :
    Deficient n ∨ Abundant n ∨ Perfect n := by
  grind [Perfect, Abundant, Deficient]

/--
theorem `Perfect.pseudoperfect` / 定理 `Perfect.pseudoperfect`

English:
theorem Perfect.pseudoperfect
  given: (h : Perfect n)
  statement: Pseudoperfect n
  proof: ⟨h.2, ⟨properDivisors n, ⟨fun _ a => a, h.1⟩⟩⟩

中文:
定理 Perfect.pseudoperfect
  条件: (h : Perfect n)
  结论: Pseudoperfect n
  证明: ⟨h.2, ⟨properDivisors n, ⟨fun _ a => a, h.1⟩⟩⟩

Depends on / 依赖: properDivisors
-/
theorem Perfect.pseudoperfect (h : Perfect n) : Pseudoperfect n :=
  ⟨h.2, ⟨properDivisors n, ⟨fun _ a => a, h.1⟩⟩⟩

/--
theorem `Prime.not_abundant` / 定理 `Prime.not_abundant`

English:
theorem Prime.not_abundant
  given: (h : Prime n)
  statement: ¬ Abundant n
  proof: fun h1 => (h.one_lt.trans h1).ne' (sum_properDivisors_eq_one_iff_prime.mpr h)

中文:
定理 Prime.not_abundant
  条件: (h : Prime n)
  结论: ¬ Abundant n
  证明: fun h1 => (h.one_lt.trans h1).ne' (sum_properDivisors_eq_one_iff_prime.mpr h)

Depends on / 依赖: h.one_lt.trans, one_lt, sum_properDivisors_eq_one_iff_prime, sum_properDivisors_eq_one_iff_prime.mpr
-/
theorem Prime.not_abundant (h : Prime n) : ¬ Abundant n :=
  fun h1 => (h.one_lt.trans h1).ne' (sum_properDivisors_eq_one_iff_prime.mpr h)

/--
theorem `Prime.not_weird` / 定理 `Prime.not_weird`

English:
theorem Prime.not_weird
  given: (h : Prime n)
  statement: ¬ Weird n
  proof: by
  grind [Weird, h.not_abundant]

中文:
定理 Prime.not_weird
  条件: (h : Prime n)
  结论: ¬ Weird n
  证明: by
  grind [Weird, h.not_abundant]

Depends on / 依赖: h.not_abundant, not_abundant
-/
theorem Prime.not_weird (h : Prime n) : ¬ Weird n := by
  grind [Weird, h.not_abundant]

/--
theorem `Prime.not_pseudoperfect` / 定理 `Prime.not_pseudoperfect`

English:
theorem Prime.not_pseudoperfect
  given: (h : Prime p)
  statement: ¬ Pseudoperfect p
  proof: by
  rw [not_pseudoperfect_iff_forall]
  refine Or.inr fun s hs => ne_of_lt (lt_of_le_of_lt ?_ h.one_lt)
  rw [Prime.properDivisors h] at hs
  simpa using Finset.sum_le_sum_of_subset hs

中文:
定理 Prime.not_pseudoperfect
  条件: (h : Prime p)
  结论: ¬ Pseudoperfect p
  证明: by
  rw [not_pseudoperfect_iff_forall]
  refine Or.inr fun s hs => ne_of_lt (lt_of_le_of_lt ?_ h.one_lt)
  rw [Prime.properDivisors h] at hs
  simpa using Finset.sum_le_sum_of_subset hs

Depends on / 依赖: Finset, Finset.sum_le_sum_of_subset, Or.inr, Prime.properDivisors, h.one_lt, lt_of_le_of_lt, ne_of_lt, not_pseudoperfect_iff_forall, one_lt, properDivisors, sum_le_sum_of_subset
-/
theorem Prime.not_pseudoperfect (h : Prime p) : ¬ Pseudoperfect p := by
  rw [not_pseudoperfect_iff_forall]
  refine Or.inr fun s hs => ne_of_lt (lt_of_le_of_lt ?_ h.one_lt)
  rw [Prime.properDivisors h] at hs
  simpa using Finset.sum_le_sum_of_subset hs

/--
theorem `Prime.not_perfect` / 定理 `Prime.not_perfect`

English:
theorem Prime.not_perfect
  given: (h : Prime p)
  statement: ¬ Perfect p
  proof: fun hp => h.not_pseudoperfect hp.pseudoperfect

中文:
定理 Prime.not_perfect
  条件: (h : Prime p)
  结论: ¬ Perfect p
  证明: fun hp => h.not_pseudoperfect hp.pseudoperfect

Depends on / 依赖: h.not_pseudoperfect, hp.pseudoperfect, not_pseudoperfect, pseudoperfect
-/
theorem Prime.not_perfect (h : Prime p) : ¬ Perfect p :=
  fun hp => h.not_pseudoperfect hp.pseudoperfect

/--
theorem `Prime.deficient_pow` / 定理 `Prime.deficient_pow`

English:
theorem Prime.deficient_pow
  given: (h : Prime n)
  statement: Deficient (n ^ m)
  proof: by
  rcases Nat.eq_zero_or_pos m with (rfl | _)
  · simpa using deficient_one
  · rw [Deficient, properDivisors_prime_pow h]
    calc
      ∑ x in Finset.map ⟨(n ^ ·), Nat.pow_right_injective h.two_le⟩ (range m), x
        = ∑ i in range m, n ^ i := by simp
      _ = (n ^ m - 1) / (n - 1) := (Nat.ge

中文:
定理 Prime.deficient_pow
  条件: (h : Prime n)
  结论: Deficient (n ^ m)
  证明: by
  rcases Nat.eq_zero_or_pos m with (rfl | _)
  · simpa using deficient_one
  · rw [Deficient, properDivisors_prime_pow h]
    calc
      ∑ x in Finset.map ⟨(n ^ ·), Nat.pow_right_injective h.two_le⟩ (range m), x
        = ∑ i in range m, n ^ i := by simp
      _ = (n ^ m - 1) / (n - 1) := (Nat.ge

Depends on / 依赖: Deficient, Finset, Finset.map, LatticeHomClass, Nat.div_le_self, Nat.eq_zero_or_pos, Nat.geomSum_eq, Nat.one_pos, Nat.pow_right_injective, Prime.pos, Prime.two_le, deficient_one, div_le_self, eq_zero_or_pos, geomSum_eq, h.two_le, one_pos, pow_pos, pow_right_injective, properDivisors_prime_pow
-/
theorem Prime.deficient_pow (h : Prime n) : Deficient (n ^ m) := by
  rcases Nat.eq_zero_or_pos m with (rfl | _)
  · simpa using deficient_one
  · rw [Deficient, properDivisors_prime_pow h]
    calc
      ∑ x in Finset.map ⟨(n ^ ·), Nat.pow_right_injective h.two_le⟩ (range m), x
        = ∑ i in range m, n ^ i := by simp
      _ = (n ^ m - 1) / (n - 1) := (Nat.geomSum_eq (Prime.two_le h) _)
      _ <= (n ^ m - 1) := Nat.div_le_self (n ^ m - 1) (n - 1)
      _ < n ^ m := sub_lt (pow_pos (Prime.pos h) m) (Nat.one_pos)

/--
theorem `_root_.IsPrimePow.deficient` / 定理 `_root_.IsPrimePow.deficient`

English:
theorem _root_.IsPrimePow.deficient
  given: (h : IsPrimePow n)
  statement: Deficient n
  proof: by
  obtain ⟨p, k, hp, -, rfl⟩ := h
  exact hp.nat_prime.deficient_pow

中文:
定理 _root_.IsPrimePow.deficient
  条件: (h : IsPrimePow n)
  结论: Deficient n
  证明: by
  obtain ⟨p, k, hp, -, rfl⟩ := h
  exact hp.nat_prime.deficient_pow

Depends on / 依赖: deficient_pow, hp.nat_prime.deficient_pow, nat_prime
-/
theorem _root_.IsPrimePow.deficient (h : IsPrimePow n) : Deficient n := by
  obtain ⟨p, k, hp, -, rfl⟩ := h
  exact hp.nat_prime.deficient_pow

/--
theorem `Prime.deficient` / 定理 `Prime.deficient`

English:
theorem Prime.deficient
  given: (h : Prime n)
  statement: Deficient n
  proof: (pow_one n) ▸ h.deficient_pow

中文:
定理 Prime.deficient
  条件: (h : Prime n)
  结论: Deficient n
  证明: (pow_one n) ▸ h.deficient_pow

Depends on / 依赖: deficient_pow, h.deficient_pow, pow_one
-/
theorem Prime.deficient (h : Prime n) : Deficient n :=
  (pow_one n) ▸ h.deficient_pow

/--
theorem `infinite_deficient` / 定理 `infinite_deficient`

English:
theorem infinite_deficient
  statement: {n : Nat | n.Deficient}.Infinite
  proof: by
  rw [Set.infinite_iff_exists_gt]
  intro a
  obtain ⟨b, h1, h2⟩ := exists_infinite_primes a.succ
  exact ⟨b, h2.deficient, h1⟩

中文:
定理 infinite_deficient
  结论: {n : 自然数 | n.Deficient}.Infinite
  证明: by
  rw [Set.infinite_iff_exists_gt]
  intro a
  obtain ⟨b, h1, h2⟩ := exists_infinite_primes a.succ
  exact ⟨b, h2.deficient, h1⟩

Depends on / 依赖: Set.infinite_iff_exists_gt, a.succ, deficient, exists_infinite_primes, h2.deficient, infinite_iff_exists_gt
-/
theorem infinite_deficient : {n : Nat | n.Deficient}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro a
  obtain ⟨b, h1, h2⟩ := exists_infinite_primes a.succ
  exact ⟨b, h2.deficient, h1⟩

/--
theorem `infinite_even_deficient` / 定理 `infinite_even_deficient`

English:
theorem infinite_even_deficient
  statement: {n : Nat | Even n ∧ n.Deficient}.Infinite
  proof: by
  rw [Set.infinite_iff_exists_gt]
  intro n
  use 2 ^ (n + 1)
  constructor
  · exact ⟨⟨2 ^ n, by rw [pow_succ, mul_two]⟩, prime_two.deficient_pow⟩
  · calc
      n <= 2 ^ n := Nat.le_of_lt n.lt_two_pow_self
      _ < 2 ^ (n + 1) := (Nat.pow_lt_pow_iff_right (Nat.one_lt_two)).mpr (lt_add_one n)

中文:
定理 infinite_even_deficient
  结论: {n : 自然数 | Even n ∧ n.Deficient}.Infinite
  证明: by
  rw [Set.infinite_iff_exists_gt]
  intro n
  use 2 ^ (n + 1)
  constructor
  · exact ⟨⟨2 ^ n, by rw [pow_succ, mul_two]⟩, prime_two.deficient_pow⟩
  · calc
      n <= 2 ^ n := Nat.le_of_lt n.lt_two_pow_self
      _ < 2 ^ (n + 1) := (Nat.pow_lt_pow_iff_right (Nat.one_lt_two)).mpr (lt_add_one n)

Depends on / 依赖: Nat.le_of_lt, Nat.one_lt_two, Nat.pow_lt_pow_iff_right, Set.infinite_iff_exists_gt, deficient_pow, infinite_iff_exists_gt, le_of_lt, lt_add_one, lt_two_pow_self, mul_two, n.lt_two_pow_self, one_lt_two, pow_lt_pow_iff_right, pow_succ, prime_two, prime_two.deficient_pow
-/
theorem infinite_even_deficient : {n : Nat | Even n ∧ n.Deficient}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  use 2 ^ (n + 1)
  constructor
  · exact ⟨⟨2 ^ n, by rw [pow_succ, mul_two]⟩, prime_two.deficient_pow⟩
  · calc
      n <= 2 ^ n := Nat.le_of_lt n.lt_two_pow_self
      _ < 2 ^ (n + 1) := (Nat.pow_lt_pow_iff_right (Nat.one_lt_two)).mpr (lt_add_one n)

/--
theorem `infinite_odd_deficient` / 定理 `infinite_odd_deficient`

English:
theorem infinite_odd_deficient
  statement: {n : Nat | Odd n ∧ n.Deficient}.Infinite
  proof: by
  rw [Set.infinite_iff_exists_gt]
  intro n
  obtain ⟨p, ⟨_, h2⟩⟩ := exists_infinite_primes (max (n + 1) 3)
  exact ⟨p, Set.mem_ofPred.mpr ⟨Prime.odd_of_ne_two h2 (Ne.symm (ne_of_lt (by grind))),
    Prime.deficient h2⟩, by grind⟩

中文:
定理 infinite_odd_deficient
  结论: {n : 自然数 | Odd n ∧ n.Deficient}.Infinite
  证明: by
  rw [Set.infinite_iff_exists_gt]
  intro n
  obtain ⟨p, ⟨_, h2⟩⟩ := exists_infinite_primes (max (n + 1) 3)
  exact ⟨p, Set.mem_ofPred.mpr ⟨Prime.odd_of_ne_two h2 (Ne.symm (ne_of_lt (by grind))),
    Prime.deficient h2⟩, by grind⟩

Depends on / 依赖: Ne.symm, Prime.deficient, Prime.odd_of_ne_two, Set.infinite_iff_exists_gt, Set.mem_ofPred.mpr, deficient, exists_infinite_primes, infinite_iff_exists_gt, mem_ofPred, ne_of_lt, odd_of_ne_two
-/
theorem infinite_odd_deficient : {n : Nat | Odd n ∧ n.Deficient}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  obtain ⟨p, ⟨_, h2⟩⟩ := exists_infinite_primes (max (n + 1) 3)
  exact ⟨p, Set.mem_ofPred.mpr ⟨Prime.odd_of_ne_two h2 (Ne.symm (ne_of_lt (by grind))),
    Prime.deficient h2⟩, by grind⟩

/--
theorem `abundant_iff_sum_divisors` / 定理 `abundant_iff_sum_divisors`

English:
theorem abundant_iff_sum_divisors
  statement: Abundant n ↔ 2 * n < ∑ i in n.divisors, i
  proof: by
  grind [Abundant, sum_divisors_eq_sum_properDivisors_add_self]

中文:
定理 abundant_iff_sum_divisors
  结论: Abundant n ↔ 2 * n < ∑ i in n.divisors, i
  证明: by
  grind [Abundant, sum_divisors_eq_sum_properDivisors_add_self]

Depends on / 依赖: Abundant, sum_divisors_eq_sum_properDivisors_add_self
-/
theorem abundant_iff_sum_divisors : Abundant n ↔ 2 * n < ∑ i in n.divisors, i := by
  grind [Abundant, sum_divisors_eq_sum_properDivisors_add_self]

/--
theorem `abundant_iff_two_lt_abundancyIndex` / 定理 `abundant_iff_two_lt_abundancyIndex`

English:
theorem abundant_iff_two_lt_abundancyIndex
  statement: Abundant n ↔ 2 < n.abundancyIndex
  proof: by
  by_cases h : n = 0
  · simp [h, Abundant, abundancyIndex]
  · rw [abundant_iff_sum_divisors, abundancyIndex, lt_div_iff₀ (by positivity)]
    norm_cast

中文:
定理 abundant_iff_two_lt_abundancyIndex
  结论: Abundant n ↔ 2 < n.abundancyIndex
  证明: by
  by_cases h : n = 0
  · simp [h, Abundant, abundancyIndex]
  · rw [abundant_iff_sum_divisors, abundancyIndex, lt_div_iff₀ (by positivity)]
    norm_cast

Depends on / 依赖: Abundant, abundancyIndex, abundant_iff_sum_divisors
-/
theorem abundant_iff_two_lt_abundancyIndex : Abundant n ↔ 2 < n.abundancyIndex := by
  by_cases h : n = 0
  · simp [h, Abundant, abundancyIndex]
  · rw [abundant_iff_sum_divisors, abundancyIndex, lt_div_iff₀ (by positivity)]
    norm_cast

/--
theorem `abundancyIndex_le_of_dvd` / 定理 `abundancyIndex_le_of_dvd`

English:
theorem abundancyIndex_le_of_dvd
  given: (hn : n != 0) (hd : m ∣ n)
  proof: by
  obtain ⟨k, hk⟩ := hd
  have hk0 : k != 0 := by grind
  rw [abundancyIndex]; rw [abundancyIndex]; rw [hk]; rw [cast_mul]; rw [div_mul_eq_div_div_swap]
  refine div_le_div_of_nonneg_right ?_ m.cast_nonneg
  rw [le_div_iff₀ (by grind [cast_pos]), ← cast_mul, cast_le, sum_mul]
  exact (sum_image (f

中文:
定理 abundancyIndex_le_of_dvd
  条件: (hn : n != 0) (hd : m ∣ n)
  证明: by
  obtain ⟨k, hk⟩ := hd
  have hk0 : k != 0 := by grind
  rw [abundancyIndex]; rw [abundancyIndex]; rw [hk]; rw [cast_mul]; rw [div_mul_eq_div_div_swap]
  refine div_le_div_of_nonneg_right ?_ m.cast_nonneg
  rw [le_div_iff₀ (by grind [cast_pos]), ← cast_mul, cast_le, sum_mul]
  exact (sum_image (f

Depends on / 依赖: abundancyIndex, cast_le, cast_mul, cast_nonneg, cast_pos, div_le_div_of_nonneg_right, div_mul_eq_div_div_swap, m.cast_nonneg, mul_dvd_mul_iff_right, sum_image, sum_le_sum_of_subset, sum_mul, symm.trans_le, trans_le
-/
theorem abundancyIndex_le_of_dvd (hn : n != 0) (hd : m ∣ n) :
    m.abundancyIndex <= n.abundancyIndex := by
  obtain ⟨k, hk⟩ := hd
  have hk0 : k != 0 := by grind
  rw [abundancyIndex]; rw [abundancyIndex]; rw [hk]; rw [cast_mul]; rw [div_mul_eq_div_div_swap]
  refine div_le_div_of_nonneg_right ?_ m.cast_nonneg
  rw [le_div_iff₀ (by grind [cast_pos]), ← cast_mul, cast_le, sum_mul]
  exact (sum_image (f := fun i => i) (mul_left_injective₀ hk0).injOn).symm.trans_le
    (sum_le_sum_of_subset (by grind [mul_dvd_mul_iff_right hk0]))

/--
theorem `Abundant.of_dvd` / 定理 `Abundant.of_dvd`

English:
theorem Abundant.of_dvd
  given: (h : Abundant m) (hd : m ∣ n) (hn : n != 0)
  statement: Abundant n
  proof: by
  have := abundancyIndex_le_of_dvd hn hd
  grind [abundant_iff_two_lt_abundancyIndex]

中文:
定理 Abundant.of_dvd
  条件: (h : Abundant m) (hd : m ∣ n) (hn : n != 0)
  结论: Abundant n
  证明: by
  have := abundancyIndex_le_of_dvd hn hd
  grind [abundant_iff_two_lt_abundancyIndex]

Depends on / 依赖: abundancyIndex_le_of_dvd, abundant_iff_two_lt_abundancyIndex
-/
theorem Abundant.of_dvd (h : Abundant m) (hd : m ∣ n) (hn : n != 0) : Abundant n := by
  have := abundancyIndex_le_of_dvd hn hd
  grind [abundant_iff_two_lt_abundancyIndex]

/--
theorem `Abundant.mul_left` / 定理 `Abundant.mul_left`

English:
theorem Abundant.mul_left
  given: (h : Abundant n) (hm : m != 0)
  statement: Abundant (m * n)
  proof: by
  have hn : n != 0 := by grind [not_abundant_zero]
  have hmn : m * n != 0 := mul_ne_zero hm hn
  exact Abundant.of_dvd h (Nat.dvd_mul_left n m) hmn

中文:
定理 Abundant.mul_left
  条件: (h : Abundant n) (hm : m != 0)
  结论: Abundant (m * n)
  证明: by
  have hn : n != 0 := by grind [not_abundant_zero]
  have hmn : m * n != 0 := mul_ne_zero hm hn
  exact Abundant.of_dvd h (Nat.dvd_mul_left n m) hmn

Depends on / 依赖: Abundant, Abundant.of_dvd, Nat.dvd_mul_left, dvd_mul_left, mul_ne_zero, not_abundant_zero, of_dvd
-/
theorem Abundant.mul_left (h : Abundant n) (hm : m != 0) : Abundant (m * n) := by
  have hn : n != 0 := by grind [not_abundant_zero]
  have hmn : m * n != 0 := mul_ne_zero hm hn
  exact Abundant.of_dvd h (Nat.dvd_mul_left n m) hmn

/--
theorem `infinite_even_abundant` / 定理 `infinite_even_abundant`

English:
theorem infinite_even_abundant
  statement: {n : Nat | Even n ∧ n.Abundant}.Infinite
  proof: by
  rw [Set.infinite_iff_exists_gt]
  intro a
  have ha : Abundant 12 := by decide
  use (2 * (a + 1)) * 12
  grind [Abundant.mul_left ha (show 2 * (a + 1) != 0 by grind)]

中文:
定理 infinite_even_abundant
  结论: {n : 自然数 | Even n ∧ n.Abundant}.Infinite
  证明: by
  rw [Set.infinite_iff_exists_gt]
  intro a
  have ha : Abundant 12 := by decide
  use (2 * (a + 1)) * 12
  grind [Abundant.mul_left ha (show 2 * (a + 1) != 0 by grind)]

Depends on / 依赖: Abundant, Abundant.mul_left, Set.infinite_iff_exists_gt, infinite_iff_exists_gt, mul_left
-/
theorem infinite_even_abundant : {n : Nat | Even n ∧ n.Abundant}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro a
  have ha : Abundant 12 := by decide
  use (2 * (a + 1)) * 12
  grind [Abundant.mul_left ha (show 2 * (a + 1) != 0 by grind)]

/--
theorem `infinite_odd_abundant` / 定理 `infinite_odd_abundant`

English:
theorem infinite_odd_abundant
  statement: {n : Nat | Odd n ∧ n.Abundant}.Infinite
  proof: by
  rw [Set.infinite_iff_exists_gt]
  intro a
  have ha : Abundant 945 := by decide +kernel
  use (2 * a + 1) * 945
  grind [Abundant.mul_left ha (show 2 * a + 1 != 0 by grind)]

中文:
定理 infinite_odd_abundant
  结论: {n : 自然数 | Odd n ∧ n.Abundant}.Infinite
  证明: by
  rw [Set.infinite_iff_exists_gt]
  intro a
  have ha : Abundant 945 := by decide +kernel
  use (2 * a + 1) * 945
  grind [Abundant.mul_left ha (show 2 * a + 1 != 0 by grind)]

Depends on / 依赖: Abundant, Abundant.mul_left, Set.infinite_iff_exists_gt, infinite_iff_exists_gt, kernel, mul_left
-/
theorem infinite_odd_abundant : {n : Nat | Odd n ∧ n.Abundant}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro a
  have ha : Abundant 945 := by decide +kernel
  use (2 * a + 1) * 945
  grind [Abundant.mul_left ha (show 2 * a + 1 != 0 by grind)]

end Nat
