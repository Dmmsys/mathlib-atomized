/-
Copyright (c) 2021 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Ralf Stephan
-/
module

public import Mathlib.Data.Nat.Prime.Nth
public import Mathlib.Data.Nat.Totient
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The Prime Counting Function

In this file we define the prime counting function: the function on natural numbers that returns
the number of primes less than or equal to its input.

## Main Results

The main definitions for this file are

- `Nat.primeCounting`: The prime counting function π
- `Nat.primeCounting'`: π(n - 1)
- `Nat.primesBelow`: The finset of primes less than n
  (this was previously in `Mathlib.NumberTheory.SmoothNumbers`)
- `Nat.primesLE`: The finset of primes less than or equal to n

We then prove that these are monotone in `Nat.monotone_primeCounting` and
`Nat.monotone_primeCounting'`. The last main theorem `Nat.primeCounting'_add_le` is an upper
bound on `π'` which arises by observing that all numbers greater than `k` and not coprime to `k`
are not prime, and so only at most `φ(k)/k` fraction of the numbers from `k` to `n` are prime.

## Notation

With `open scoped Nat.Prime`, we use the standard notation `π` to represent the prime counting
function (and `π'` to represent the reindexed version).

-/

@[expose] public section


namespace Nat

open Finset

/--
Definition of `primeCounting'` / `primeCounting'` 的定义

English:
definition primeCounting'
  signature: : Nat -> Nat
  body: Nat.count Prime

中文:
定义 primeCounting'
  签名: : 自然数 -> 自然数
  定义体: Nat.count Prime

Depends on / 依赖: Nat.count
-/
def primeCounting' : Nat -> Nat :=
  Nat.count Prime

/--
Definition of `primeCounting` / `primeCounting` 的定义

English:
definition primeCounting
  signature: (n : Nat)
  body: primeCounting' (n + 1)

@[inherit_doc] scoped[Nat.Prime] notation "π" => Nat.primeCounting

@[inherit_doc] scoped[Nat.Prime] notation "π'" => Nat.primeCounting'

中文:
定义 primeCounting
  签名: (n : 自然数)
  定义体: primeCounting' (n + 1)

@[inherit_doc] scoped[Nat.Prime] notation "π" => Nat.primeCounting

@[inherit_doc] scoped[Nat.Prime] notation "π'" => Nat.primeCounting'

Depends on / 依赖: primeCounting
-/
def primeCounting (n : Nat) : Nat :=
  primeCounting' (n + 1)

@[inherit_doc] scoped[Nat.Prime] notation "π" => Nat.primeCounting

@[inherit_doc] scoped[Nat.Prime] notation "π'" => Nat.primeCounting'

open scoped Nat.Prime

/--
theorem `primeCounting_eq_primeCounting'_succ` / 定理 `primeCounting_eq_primeCounting'_succ`

English:
theorem primeCounting_eq_primeCounting'_succ
  given: (n : Nat)
  statement: π n = π' (n + 1)
  proof: rfl

@[simp]

中文:
定理 primeCounting_eq_primeCounting'_succ
  条件: (n : 自然数)
  结论: π n = π' (n + 1)
  证明: rfl

@[simp]
-/
theorem primeCounting_eq_primeCounting'_succ (n : Nat) : π n = π' (n + 1) := rfl

@[simp]
/--
theorem `primeCounting_sub_one` / 定理 `primeCounting_sub_one`

English:
theorem primeCounting_sub_one
  given: (n : Nat)
  statement: π (n - 1) = π' n
  proof: by
  cases n <;> rfl

中文:
定理 primeCounting_sub_one
  条件: (n : 自然数)
  结论: π (n - 1) = π' n
  证明: by
  cases n <;> rfl
-/
theorem primeCounting_sub_one (n : Nat) : π (n - 1) = π' n := by
  cases n <;> rfl

/--
theorem `monotone_primeCounting'` / 定理 `monotone_primeCounting'`

English:
theorem monotone_primeCounting'
  statement: Monotone primeCounting'
  proof: count_monotone Prime

中文:
定理 monotone_primeCounting'
  结论: 递增 primeCounting'
  证明: count_monotone Prime

Depends on / 依赖: count_monotone
-/
theorem monotone_primeCounting' : Monotone primeCounting' :=
  count_monotone Prime

/--
theorem `monotone_primeCounting` / 定理 `monotone_primeCounting`

English:
theorem monotone_primeCounting
  statement: Monotone primeCounting
  proof: monotone_primeCounting'.comp (monotone_id.add_const _)

@[simp]

中文:
定理 monotone_primeCounting
  结论: 递增 primeCounting
  证明: monotone_primeCounting'.comp (monotone_id.add_const _)

@[simp]

Depends on / 依赖: add_const, monotone_id, monotone_id.add_const, monotone_primeCounting
-/
theorem monotone_primeCounting : Monotone primeCounting :=
  monotone_primeCounting'.comp (monotone_id.add_const _)

@[simp]
/--
theorem `primeCounting'_nth_eq` / 定理 `primeCounting'_nth_eq`

English:
theorem primeCounting'_nth_eq
  given: (n : Nat)
  statement: π' (nth Prime n) = n
  proof: count_nth_of_infinite infinite_setOfPred_prime _

中文:
定理 primeCounting'_nth_eq
  条件: (n : 自然数)
  结论: π' (nth 素 n) = n
  证明: count_nth_of_infinite infinite_setOfPred_prime _
-/
theorem primeCounting'_nth_eq (n : Nat) : π' (nth Prime n) = n :=
  count_nth_of_infinite infinite_setOfPred_prime _

/--
theorem `add_two_le_nth_prime` / 定理 `add_two_le_nth_prime`

English:
theorem add_two_le_nth_prime
  given: (n : Nat)
  statement: n + 2 <= nth Prime n
  proof: nth_prime_zero_eq_two ▸ (nth_strictMono infinite_setOfPred_prime).add_le_nat n 0

中文:
定理 add_two_le_nth_prime
  条件: (n : 自然数)
  结论: n + 2 <= nth 素 n
  证明: nth_prime_zero_eq_two ▸ (nth_strictMono infinite_setOfPred_prime).add_le_nat n 0

Depends on / 依赖: add_le_nat, infinite_setOfPred_prime, nth_prime_zero_eq_two, nth_strictMono
-/
theorem add_two_le_nth_prime (n : Nat) : n + 2 <= nth Prime n :=
  nth_prime_zero_eq_two ▸ (nth_strictMono infinite_setOfPred_prime).add_le_nat n 0

/--
theorem `surjective_primeCounting'` / 定理 `surjective_primeCounting'`

English:
theorem surjective_primeCounting'
  statement: Function.Surjective π'
  proof: Nat.surjective_count_of_infinite_setOfPred infinite_setOfPred_prime

中文:
定理 surjective_primeCounting'
  结论: 函数.满射 π'
  证明: Nat.surjective_count_of_infinite_setOfPred infinite_setOfPred_prime

Depends on / 依赖: Nat.surjective_count_of_infinite_setOfPred, infinite_setOfPred_prime, surjective_count_of_infinite_setOfPred
-/
theorem surjective_primeCounting' : Function.Surjective π' :=
  Nat.surjective_count_of_infinite_setOfPred infinite_setOfPred_prime

/--
theorem `surjective_primeCounting` / 定理 `surjective_primeCounting`

English:
theorem surjective_primeCounting
  statement: Function.Surjective π
  proof: by
  suffices Function.Surjective (π ∘ fun n => n - 1) from this.of_comp
  convert! surjective_primeCounting'
  ext
  exact primeCounting_sub_one _

中文:
定理 surjective_primeCounting
  结论: 函数.满射 π
  证明: by
  suffices Function.Surjective (π ∘ fun n => n - 1) from this.of_comp
  convert! surjective_primeCounting'
  ext
  exact primeCounting_sub_one _

Depends on / 依赖: Function, Function.Surjective, Surjective, convert, of_comp, primeCounting_sub_one, surjective_primeCounting, this.of_comp
-/
theorem surjective_primeCounting : Function.Surjective π := by
  suffices Function.Surjective (π ∘ fun n => n - 1) from this.of_comp
  convert! surjective_primeCounting'
  ext
  exact primeCounting_sub_one _

open Filter

/--
theorem `tendsto_primeCounting'` / 定理 `tendsto_primeCounting'`

English:
theorem tendsto_primeCounting'
  statement: Tendsto π' atTop atTop
  proof: by
  apply tendsto_atTop_atTop_of_monotone' monotone_primeCounting'
  simp [Set.range_eq_univ.mpr surjective_primeCounting']

中文:
定理 tendsto_primeCounting'
  结论: 收敛 π' atTop atTop
  证明: by
  apply tendsto_atTop_atTop_of_monotone' monotone_primeCounting'
  simp [Set.range_eq_univ.mpr surjective_primeCounting']

Depends on / 依赖: Set.range_eq_univ.mpr, monotone_primeCounting, range_eq_univ, surjective_primeCounting, tendsto_atTop_atTop_of_monotone
-/
theorem tendsto_primeCounting' : Tendsto π' atTop atTop := by
  apply tendsto_atTop_atTop_of_monotone' monotone_primeCounting'
  simp [Set.range_eq_univ.mpr surjective_primeCounting']

/--
theorem `tendsto_primeCounting` / 定理 `tendsto_primeCounting`

English:
theorem tendsto_primeCounting
  statement: Tendsto π atTop atTop
  proof: (tendsto_add_atTop_iff_nat 1).mpr tendsto_primeCounting'

@[simp]

中文:
定理 tendsto_primeCounting
  结论: 收敛 π atTop atTop
  证明: (tendsto_add_atTop_iff_nat 1).mpr tendsto_primeCounting'

@[simp]

Depends on / 依赖: tendsto_add_atTop_iff_nat, tendsto_primeCounting
-/
theorem tendsto_primeCounting : Tendsto π atTop atTop :=
  (tendsto_add_atTop_iff_nat 1).mpr tendsto_primeCounting'

@[simp]
/--
theorem `prime_nth_prime` / 定理 `prime_nth_prime`

English:
theorem prime_nth_prime
  given: (n : Nat)
  statement: Prime (nth Prime n)
  proof: nth_mem_of_infinite infinite_setOfPred_prime _

@[simp]

中文:
定理 prime_nth_prime
  条件: (n : 自然数)
  结论: 素 (nth 素 n)
  证明: nth_mem_of_infinite infinite_setOfPred_prime _

@[simp]

Depends on / 依赖: infinite_setOfPred_prime, nth_mem_of_infinite
-/
theorem prime_nth_prime (n : Nat) : Prime (nth Prime n) :=
  nth_mem_of_infinite infinite_setOfPred_prime _

@[simp]
/--
lemma `primeCounting'_eq_zero_iff` / 引理 `primeCounting'_eq_zero_iff`

English:
lemma primeCounting'_eq_zero_iff
  given: {n : Nat}
  statement: n.primeCounting' = 0 ↔ n <= 2
  proof: by
  rw [primeCounting']; rw [Nat.count_eq_zero ⟨_]; rw [Nat.prime_two⟩]; rw [Nat.nth_prime_zero_eq_two]

@[simp]

中文:
引理 primeCounting'_eq_zero_iff
  条件: {n : 自然数}
  结论: n.primeCounting' = 0 ↔ n <= 2
  证明: by
  rw [primeCounting']; rw [Nat.count_eq_zero ⟨_]; rw [Nat.prime_two⟩]; rw [Nat.nth_prime_zero_eq_two]

@[simp]
-/
lemma primeCounting'_eq_zero_iff {n : Nat} : n.primeCounting' = 0 ↔ n <= 2 := by
  rw [primeCounting']; rw [Nat.count_eq_zero ⟨_]; rw [Nat.prime_two⟩]; rw [Nat.nth_prime_zero_eq_two]

@[simp]
/--
lemma `primeCounting_eq_zero_iff` / 引理 `primeCounting_eq_zero_iff`

English:
lemma primeCounting_eq_zero_iff
  given: {n : Nat}
  statement: n.primeCounting = 0 ↔ n <= 1
  proof: by
  simp [primeCounting, -Order.add_one_le_iff]

@[simp]

中文:
引理 primeCounting_eq_zero_iff
  条件: {n : 自然数}
  结论: n.primeCounting = 0 ↔ n <= 1
  证明: by
  simp [primeCounting, -Order.add_one_le_iff]

@[simp]

Depends on / 依赖: Order.add_one_le_iff, add_one_le_iff, primeCounting
-/
lemma primeCounting_eq_zero_iff {n : Nat} : n.primeCounting = 0 ↔ n <= 1 := by
  simp [primeCounting, -Order.add_one_le_iff]

@[simp]
/--
lemma `primeCounting_zero` / 引理 `primeCounting_zero`

English:
lemma primeCounting_zero
  statement: primeCounting 0 = 0
  proof: primeCounting_eq_zero_iff.mpr zero_le_one

@[simp]

中文:
引理 primeCounting_zero
  结论: primeCounting 0 = 0
  证明: primeCounting_eq_zero_iff.mpr zero_le_one

@[simp]

Depends on / 依赖: primeCounting_eq_zero_iff, primeCounting_eq_zero_iff.mpr, zero_le_one
-/
lemma primeCounting_zero : primeCounting 0 = 0 :=
  primeCounting_eq_zero_iff.mpr zero_le_one

@[simp]
/--
lemma `primeCounting_one` / 引理 `primeCounting_one`

English:
lemma primeCounting_one
  statement: primeCounting 1 = 0
  proof: primeCounting_eq_zero_iff.mpr le_rfl

中文:
引理 primeCounting_one
  结论: primeCounting 1 = 0
  证明: primeCounting_eq_zero_iff.mpr le_rfl

Depends on / 依赖: le_rfl, primeCounting_eq_zero_iff, primeCounting_eq_zero_iff.mpr
-/
lemma primeCounting_one : primeCounting 1 = 0 :=
  primeCounting_eq_zero_iff.mpr le_rfl

section PrimeSets

variable {p k n : Nat}

/--
Definition of `primesBelow` / `primesBelow` 的定义

English:
definition primesBelow
  signature: (n : Nat)
  body: {p in Finset.range n | p.Prime}

中文:
定义 primesBelow
  签名: (n : 自然数)
  定义体: {p in Finset.range n | p.Prime}

Depends on / 依赖: Finset, Finset.range, p.Prime
-/
def primesBelow (n : Nat) : Finset Nat := {p in Finset.range n | p.Prime}

/--
Definition of `primesLE` / `primesLE` 的定义

English:
definition primesLE
  signature: (n : Nat)
  body: primesBelow (n + 1)

中文:
定义 primesLE
  签名: (n : 自然数)
  定义体: primesBelow (n + 1)

Depends on / 依赖: primesBelow
-/
def primesLE (n : Nat) : Finset Nat := primesBelow (n + 1)

/--
lemma `primesBelow_eq_filter_range` / 引理 `primesBelow_eq_filter_range`

English:
lemma primesBelow_eq_filter_range
  given: (n : Nat)
  statement: primesBelow n = filter Nat.Prime (range n)
  proof: rfl

中文:
引理 primesBelow_eq_filter_range
  条件: (n : 自然数)
  结论: primesBelow n = filter 自然数.素 (range n)
  证明: rfl
-/
lemma primesBelow_eq_filter_range (n : Nat) : primesBelow n = filter Nat.Prime (range n) := rfl

/--
lemma `primesLE_eq_filter_range` / 引理 `primesLE_eq_filter_range`

English:
lemma primesLE_eq_filter_range
  given: (n : Nat)
  statement: primesLE n = filter Nat.Prime (range (n + 1))
  proof: rfl

@[simp]

中文:
引理 primesLE_eq_filter_range
  条件: (n : 自然数)
  结论: primesLE n = filter 自然数.素 (range (n + 1))
  证明: rfl

@[simp]
-/
lemma primesLE_eq_filter_range (n : Nat) : primesLE n = filter Nat.Prime (range (n + 1)) := rfl

@[simp]
/--
lemma `primesBelow_zero` / 引理 `primesBelow_zero`

English:
lemma primesBelow_zero
  statement: primesBelow 0 = ∅
  proof: by
  decide

@[simp]

中文:
引理 primesBelow_zero
  结论: primesBelow 0 = ∅
  证明: by
  decide

@[simp]
-/
lemma primesBelow_zero : primesBelow 0 = ∅ := by
  decide

@[simp]
/--
lemma `primesBelow_one` / 引理 `primesBelow_one`

English:
lemma primesBelow_one
  statement: primesBelow 1 = ∅
  proof: by
  decide

@[simp]

中文:
引理 primesBelow_one
  结论: primesBelow 1 = ∅
  证明: by
  decide

@[simp]
-/
lemma primesBelow_one : primesBelow 1 = ∅ := by
  decide

@[simp]
/--
lemma `primesBelow_two` / 引理 `primesBelow_two`

English:
lemma primesBelow_two
  statement: primesBelow 2 = ∅
  proof: by
  decide

@[simp]

中文:
引理 primesBelow_two
  结论: primesBelow 2 = ∅
  证明: by
  decide

@[simp]
-/
lemma primesBelow_two : primesBelow 2 = ∅ := by
  decide

@[simp]
/--
lemma `primesLE_zero` / 引理 `primesLE_zero`

English:
lemma primesLE_zero
  statement: primesLE 0 = ∅
  proof: primesBelow_one

@[simp]

中文:
引理 primesLE_zero
  结论: primesLE 0 = ∅
  证明: primesBelow_one

@[simp]

Depends on / 依赖: primesBelow_one
-/
lemma primesLE_zero : primesLE 0 = ∅ := primesBelow_one

@[simp]
/--
lemma `primesLE_one` / 引理 `primesLE_one`

English:
lemma primesLE_one
  statement: primesLE 1 = ∅
  proof: primesBelow_two

中文:
引理 primesLE_one
  结论: primesLE 1 = ∅
  证明: primesBelow_two

Depends on / 依赖: primesBelow_two
-/
lemma primesLE_one : primesLE 1 = ∅ := primesBelow_two

/--
theorem `primesBelow_eq_primesLE_sub_one` / 定理 `primesBelow_eq_primesLE_sub_one`

English:
theorem primesBelow_eq_primesLE_sub_one
  given: (n : Nat)
  statement: primesBelow n = primesLE (n - 1)
  proof: by
  cases n <;> simp [primesLE]

中文:
定理 primesBelow_eq_primesLE_sub_one
  条件: (n : 自然数)
  结论: primesBelow n = primesLE (n - 1)
  证明: by
  cases n <;> simp [primesLE]

Depends on / 依赖: primesLE
-/
theorem primesBelow_eq_primesLE_sub_one (n : Nat) : primesBelow n = primesLE (n - 1) := by
  cases n <;> simp [primesLE]

/--
lemma `mem_primesBelow` / 引理 `mem_primesBelow`

English:
lemma mem_primesBelow
  proof: by simp [primesBelow]

中文:
引理 mem_primesBelow
  证明: by simp [primesBelow]

Depends on / 依赖: primesBelow
-/
lemma mem_primesBelow :
    n in primesBelow k ↔ n < k ∧ n.Prime := by simp [primesBelow]

/--
lemma `mem_primesLE` / 引理 `mem_primesLE`

English:
lemma mem_primesLE
  statement: p in primesLE n ↔ p <= n ∧ p.Prime
  proof: by
  simp [primesLE, mem_primesBelow]

中文:
引理 mem_primesLE
  结论: p in primesLE n ↔ p <= n ∧ p.素
  证明: by
  simp [primesLE, mem_primesBelow]

Depends on / 依赖: mem_primesBelow, primesLE
-/
lemma mem_primesLE : p in primesLE n ↔ p <= n ∧ p.Prime := by
  simp [primesLE, mem_primesBelow]

/--
lemma `prime_of_mem_primesBelow` / 引理 `prime_of_mem_primesBelow`

English:
lemma prime_of_mem_primesBelow
  given: (h : p in n.primesBelow)
  statement: p.Prime
  proof: (Finset.mem_filter.mp h).2

中文:
引理 prime_of_mem_primesBelow
  条件: (h : p in n.primesBelow)
  结论: p.素
  证明: (Finset.mem_filter.mp h).2

Depends on / 依赖: Finset, Finset.mem_filter.mp, mem_filter
-/
lemma prime_of_mem_primesBelow (h : p in n.primesBelow) : p.Prime :=
  (Finset.mem_filter.mp h).2

/--
lemma `prime_of_mem_primesLE` / 引理 `prime_of_mem_primesLE`

English:
lemma prime_of_mem_primesLE
  given: (hp : p in primesLE n)
  statement: p.Prime
  proof: prime_of_mem_primesBelow hp

中文:
引理 prime_of_mem_primesLE
  条件: (hp : p in primesLE n)
  结论: p.素
  证明: prime_of_mem_primesBelow hp

Depends on / 依赖: prime_of_mem_primesBelow
-/
lemma prime_of_mem_primesLE (hp : p in primesLE n) : p.Prime :=
  prime_of_mem_primesBelow hp

/--
lemma `lt_of_mem_primesBelow` / 引理 `lt_of_mem_primesBelow`

English:
lemma lt_of_mem_primesBelow
  given: (h : p in n.primesBelow)
  statement: p < n
  proof: Finset.mem_range.mp Finset.mem_of_mem_filter p h

中文:
引理 lt_of_mem_primesBelow
  条件: (h : p in n.primesBelow)
  结论: p < n
  证明: Finset.mem_range.mp Finset.mem_of_mem_filter p h

Depends on / 依赖: Finset, Finset.mem_of_mem_filter, Finset.mem_range.mp, mem_of_mem_filter, mem_range
-/
lemma lt_of_mem_primesBelow (h : p in n.primesBelow) : p < n :=
Finset.mem_range.mp Finset.mem_of_mem_filter p h

/--
lemma `le_of_mem_primesLE` / 引理 `le_of_mem_primesLE`

English:
lemma le_of_mem_primesLE
  given: (hp : p in primesLE n)
  statement: p <= n
  proof: (mem_primesLE.mp hp).1

中文:
引理 le_of_mem_primesLE
  条件: (hp : p in primesLE n)
  结论: p <= n
  证明: (mem_primesLE.mp hp).1

Depends on / 依赖: mem_primesLE, mem_primesLE.mp
-/
lemma le_of_mem_primesLE (hp : p in primesLE n) : p <= n := (mem_primesLE.mp hp).1

/--
lemma `one_lt_of_mem_primesBelow` / 引理 `one_lt_of_mem_primesBelow`

English:
lemma one_lt_of_mem_primesBelow
  given: (hp : p in primesBelow n)
  statement: 1 < p
  proof: (prime_of_mem_primesBelow hp).one_lt

中文:
引理 one_lt_of_mem_primesBelow
  条件: (hp : p in primesBelow n)
  结论: 1 < p
  证明: (prime_of_mem_primesBelow hp).one_lt

Depends on / 依赖: one_lt, prime_of_mem_primesBelow
-/
lemma one_lt_of_mem_primesBelow (hp : p in primesBelow n) : 1 < p :=
  (prime_of_mem_primesBelow hp).one_lt

/--
lemma `one_lt_of_mem_primesLE` / 引理 `one_lt_of_mem_primesLE`

English:
lemma one_lt_of_mem_primesLE
  given: (hp : p in primesLE n)
  statement: 1 < p
  proof: one_lt_of_mem_primesBelow hp

中文:
引理 one_lt_of_mem_primesLE
  条件: (hp : p in primesLE n)
  结论: 1 < p
  证明: one_lt_of_mem_primesBelow hp

Depends on / 依赖: one_lt_of_mem_primesBelow
-/
lemma one_lt_of_mem_primesLE (hp : p in primesLE n) : 1 < p :=
  one_lt_of_mem_primesBelow hp

/--
lemma `two_le_of_mem_primesBelow` / 引理 `two_le_of_mem_primesBelow`

English:
lemma two_le_of_mem_primesBelow
  given: (hp : p in primesBelow n)
  statement: 2 <= p
  proof: (prime_of_mem_primesBelow hp).two_le

中文:
引理 two_le_of_mem_primesBelow
  条件: (hp : p in primesBelow n)
  结论: 2 <= p
  证明: (prime_of_mem_primesBelow hp).two_le

Depends on / 依赖: prime_of_mem_primesBelow, two_le
-/
lemma two_le_of_mem_primesBelow (hp : p in primesBelow n) : 2 <= p :=
  (prime_of_mem_primesBelow hp).two_le

/--
lemma `two_le_of_mem_primesLE` / 引理 `two_le_of_mem_primesLE`

English:
lemma two_le_of_mem_primesLE
  given: (hp : p in primesLE n)
  statement: 2 <= p
  proof: two_le_of_mem_primesBelow hp

中文:
引理 two_le_of_mem_primesLE
  条件: (hp : p in primesLE n)
  结论: 2 <= p
  证明: two_le_of_mem_primesBelow hp

Depends on / 依赖: two_le_of_mem_primesBelow
-/
lemma two_le_of_mem_primesLE (hp : p in primesLE n) : 2 <= p :=
  two_le_of_mem_primesBelow hp

/--
lemma `primesBelow_eq_filter_Ico_zero` / 引理 `primesBelow_eq_filter_Ico_zero`

English:
lemma primesBelow_eq_filter_Ico_zero
  given: (n : Nat)
  statement: primesBelow n = filter Nat.Prime (Ico 0 n)
  proof: by
  ext p
  simp [primesBelow_eq_filter_range]

中文:
引理 primesBelow_eq_filter_Ico_zero
  条件: (n : 自然数)
  结论: primesBelow n = filter 自然数.素 (左闭右开区间 0 n)
  证明: by
  ext p
  simp [primesBelow_eq_filter_range]

Depends on / 依赖: primesBelow_eq_filter_range
-/
lemma primesBelow_eq_filter_Ico_zero (n : Nat) : primesBelow n = filter Nat.Prime (Ico 0 n) := by
  ext p
  simp [primesBelow_eq_filter_range]

/--
lemma `primesLE_eq_filter_Icc_zero` / 引理 `primesLE_eq_filter_Icc_zero`

English:
lemma primesLE_eq_filter_Icc_zero
  given: (n : Nat)
  statement: primesLE n = filter Nat.Prime (Icc 0 n)
  proof: by
  ext p
  simp [primesLE_eq_filter_range]

中文:
引理 primesLE_eq_filter_Icc_zero
  条件: (n : 自然数)
  结论: primesLE n = filter 自然数.素 (闭区间 0 n)
  证明: by
  ext p
  simp [primesLE_eq_filter_range]

Depends on / 依赖: primesLE_eq_filter_range
-/
lemma primesLE_eq_filter_Icc_zero (n : Nat) : primesLE n = filter Nat.Prime (Icc 0 n) := by
  ext p
  simp [primesLE_eq_filter_range]

/--
lemma `primesBelow_eq_filter_Ioo_zero` / 引理 `primesBelow_eq_filter_Ioo_zero`

English:
lemma primesBelow_eq_filter_Ioo_zero
  given: (n : Nat)
  statement: primesBelow n = filter Nat.Prime (Ioo 0 n)
  proof: by
  ext p
  simp +contextual [primesBelow_eq_filter_range, Nat.Prime.pos]

中文:
引理 primesBelow_eq_filter_Ioo_zero
  条件: (n : 自然数)
  结论: primesBelow n = filter 自然数.素 (开区间 0 n)
  证明: by
  ext p
  simp +contextual [primesBelow_eq_filter_range, Nat.Prime.pos]

Depends on / 依赖: Nat.Prime.pos, contextual, primesBelow_eq_filter_range
-/
lemma primesBelow_eq_filter_Ioo_zero (n : Nat) : primesBelow n = filter Nat.Prime (Ioo 0 n) := by
  ext p
  simp +contextual [primesBelow_eq_filter_range, Nat.Prime.pos]

/--
lemma `primesLE_eq_filter_Ioc_zero` / 引理 `primesLE_eq_filter_Ioc_zero`

English:
lemma primesLE_eq_filter_Ioc_zero
  given: (n : Nat)
  statement: primesLE n = filter Nat.Prime (Ioc 0 n)
  proof: by
  ext p
  simp +contextual [primesLE_eq_filter_range, Nat.Prime.pos]

中文:
引理 primesLE_eq_filter_Ioc_zero
  条件: (n : 自然数)
  结论: primesLE n = filter 自然数.素 (左开右闭区间 0 n)
  证明: by
  ext p
  simp +contextual [primesLE_eq_filter_range, Nat.Prime.pos]

Depends on / 依赖: Nat.Prime.pos, contextual, primesLE_eq_filter_range
-/
lemma primesLE_eq_filter_Ioc_zero (n : Nat) : primesLE n = filter Nat.Prime (Ioc 0 n) := by
  ext p
  simp +contextual [primesLE_eq_filter_range, Nat.Prime.pos]

/--
lemma `primesBelow_eq_filter_Ico_one` / 引理 `primesBelow_eq_filter_Ico_one`

English:
lemma primesBelow_eq_filter_Ico_one
  given: (n : Nat)
  statement: primesBelow n = filter Nat.Prime (Ico 1 n)
  proof: by
  ext p
  simp +contextual [primesBelow_eq_filter_range, Nat.Prime.one_le]

中文:
引理 primesBelow_eq_filter_Ico_one
  条件: (n : 自然数)
  结论: primesBelow n = filter 自然数.素 (左闭右开区间 1 n)
  证明: by
  ext p
  simp +contextual [primesBelow_eq_filter_range, Nat.Prime.one_le]

Depends on / 依赖: Nat.Prime.one_le, contextual, one_le, primesBelow_eq_filter_range
-/
lemma primesBelow_eq_filter_Ico_one (n : Nat) : primesBelow n = filter Nat.Prime (Ico 1 n) := by
  ext p
  simp +contextual [primesBelow_eq_filter_range, Nat.Prime.one_le]

/--
lemma `primesLE_eq_filter_Icc_one` / 引理 `primesLE_eq_filter_Icc_one`

English:
lemma primesLE_eq_filter_Icc_one
  given: (n : Nat)
  statement: primesLE n = filter Nat.Prime (Icc 1 n)
  proof: by
  ext p
  simp +contextual [primesLE_eq_filter_range, Nat.Prime.one_le]

中文:
引理 primesLE_eq_filter_Icc_one
  条件: (n : 自然数)
  结论: primesLE n = filter 自然数.素 (闭区间 1 n)
  证明: by
  ext p
  simp +contextual [primesLE_eq_filter_range, Nat.Prime.one_le]

Depends on / 依赖: Nat.Prime.one_le, contextual, one_le, primesLE_eq_filter_range
-/
lemma primesLE_eq_filter_Icc_one (n : Nat) : primesLE n = filter Nat.Prime (Icc 1 n) := by
  ext p
  simp +contextual [primesLE_eq_filter_range, Nat.Prime.one_le]

/--
lemma `primesBelow_eq_filter_Ioo_one` / 引理 `primesBelow_eq_filter_Ioo_one`

English:
lemma primesBelow_eq_filter_Ioo_one
  given: (n : Nat)
  statement: primesBelow n = filter Nat.Prime (Ioo 1 n)
  proof: by
  ext p
  simp +contextual [primesBelow_eq_filter_range, Nat.Prime.one_lt]

中文:
引理 primesBelow_eq_filter_Ioo_one
  条件: (n : 自然数)
  结论: primesBelow n = filter 自然数.素 (开区间 1 n)
  证明: by
  ext p
  simp +contextual [primesBelow_eq_filter_range, Nat.Prime.one_lt]

Depends on / 依赖: Nat.Prime.one_lt, contextual, one_lt, primesBelow_eq_filter_range
-/
lemma primesBelow_eq_filter_Ioo_one (n : Nat) : primesBelow n = filter Nat.Prime (Ioo 1 n) := by
  ext p
  simp +contextual [primesBelow_eq_filter_range, Nat.Prime.one_lt]

/--
lemma `primesLE_eq_filter_Ioc_one` / 引理 `primesLE_eq_filter_Ioc_one`

English:
lemma primesLE_eq_filter_Ioc_one
  given: (n : Nat)
  statement: primesLE n = filter Nat.Prime (Ioc 1 n)
  proof: by
  ext p
  simp +contextual [primesLE_eq_filter_range, Nat.Prime.one_lt]

中文:
引理 primesLE_eq_filter_Ioc_one
  条件: (n : 自然数)
  结论: primesLE n = filter 自然数.素 (左开右闭区间 1 n)
  证明: by
  ext p
  simp +contextual [primesLE_eq_filter_range, Nat.Prime.one_lt]

Depends on / 依赖: Nat.Prime.one_lt, contextual, one_lt, primesLE_eq_filter_range
-/
lemma primesLE_eq_filter_Ioc_one (n : Nat) : primesLE n = filter Nat.Prime (Ioc 1 n) := by
  ext p
  simp +contextual [primesLE_eq_filter_range, Nat.Prime.one_lt]

/--
lemma `primesBelow_eq_filter_Ico_two` / 引理 `primesBelow_eq_filter_Ico_two`

English:
lemma primesBelow_eq_filter_Ico_two
  given: (n : Nat)
  statement: primesBelow n = filter Nat.Prime (Ico 2 n)
  proof: by
  ext p
  simp +contextual [primesBelow_eq_filter_range, Nat.Prime.two_le]

中文:
引理 primesBelow_eq_filter_Ico_two
  条件: (n : 自然数)
  结论: primesBelow n = filter 自然数.素 (左闭右开区间 2 n)
  证明: by
  ext p
  simp +contextual [primesBelow_eq_filter_range, Nat.Prime.two_le]

Depends on / 依赖: Nat.Prime.two_le, contextual, primesBelow_eq_filter_range, two_le
-/
lemma primesBelow_eq_filter_Ico_two (n : Nat) : primesBelow n = filter Nat.Prime (Ico 2 n) := by
  ext p
  simp +contextual [primesBelow_eq_filter_range, Nat.Prime.two_le]

/--
lemma `primesLE_eq_filter_Icc_two` / 引理 `primesLE_eq_filter_Icc_two`

English:
lemma primesLE_eq_filter_Icc_two
  given: (n : Nat)
  statement: primesLE n = filter Nat.Prime (Icc 2 n)
  proof: by
  ext p
  simp +contextual [primesLE_eq_filter_range, Nat.Prime.two_le]

中文:
引理 primesLE_eq_filter_Icc_two
  条件: (n : 自然数)
  结论: primesLE n = filter 自然数.素 (闭区间 2 n)
  证明: by
  ext p
  simp +contextual [primesLE_eq_filter_range, Nat.Prime.two_le]

Depends on / 依赖: Nat.Prime.two_le, contextual, primesLE_eq_filter_range, two_le
-/
lemma primesLE_eq_filter_Icc_two (n : Nat) : primesLE n = filter Nat.Prime (Icc 2 n) := by
  ext p
  simp +contextual [primesLE_eq_filter_range, Nat.Prime.two_le]

/--
lemma `primesBelow_mono` / 引理 `primesBelow_mono`

English:
lemma primesBelow_mono
  statement: Monotone primesBelow
  proof: by
  intros n m _ p
  simp [mem_primesBelow]; grind

中文:
引理 primesBelow_mono
  结论: 递增 primesBelow
  证明: by
  intros n m _ p
  simp [mem_primesBelow]; grind

Depends on / 依赖: intros, mem_primesBelow
-/
lemma primesBelow_mono : Monotone primesBelow := by
  intros n m _ p
  simp [mem_primesBelow]; grind

/--
lemma `primesLE_mono` / 引理 `primesLE_mono`

English:
lemma primesLE_mono
  statement: Monotone primesLE
  proof: by
  intros n m _ p
  simp [mem_primesLE]; grind

中文:
引理 primesLE_mono
  结论: 递增 primesLE
  证明: by
  intros n m _ p
  simp [mem_primesLE]; grind

Depends on / 依赖: intros, mem_primesLE
-/
lemma primesLE_mono : Monotone primesLE := by
  intros n m _ p
  simp [mem_primesLE]; grind

/--
lemma `primesBelow_succ` / 引理 `primesBelow_succ`

English:
lemma primesBelow_succ
  given: (n : Nat)
  proof: by
  rw [primesBelow]; rw [primesBelow]; rw [Finset.range_add_one]; rw [Finset.filter_insert]

中文:
引理 primesBelow_succ
  条件: (n : 自然数)
  证明: by
  rw [primesBelow]; rw [primesBelow]; rw [Finset.range_add_one]; rw [Finset.filter_insert]

Depends on / 依赖: Finset, Finset.filter_insert, Finset.range_add_one, filter_insert, primesBelow, range_add_one
-/
lemma primesBelow_succ (n : Nat) :
    primesBelow (n + 1) = if n.Prime then insert n (primesBelow n) else primesBelow n := by
  rw [primesBelow]; rw [primesBelow]; rw [Finset.range_add_one]; rw [Finset.filter_insert]

/--
lemma `primesLE_succ` / 引理 `primesLE_succ`

English:
lemma primesLE_succ
  given: (n : Nat)
  proof: primesBelow_succ (n + 1)

中文:
引理 primesLE_succ
  条件: (n : 自然数)
  证明: primesBelow_succ (n + 1)

Depends on / 依赖: primesBelow_succ
-/
lemma primesLE_succ (n : Nat) :
    primesLE (n + 1) = if (n + 1).Prime then insert (n + 1) (primesLE n) else primesLE n :=
  primesBelow_succ (n + 1)

/--
lemma `notMem_primesBelow` / 引理 `notMem_primesBelow`

English:
lemma notMem_primesBelow
  given: (n : Nat)
  statement: n ∉ primesBelow n
  proof: fun hn => (lt_of_mem_primesBelow hn).false

中文:
引理 notMem_primesBelow
  条件: (n : 自然数)
  结论: n ∉ primesBelow n
  证明: fun hn => (lt_of_mem_primesBelow hn).false

Depends on / 依赖: lt_of_mem_primesBelow
-/
lemma notMem_primesBelow (n : Nat) : n ∉ primesBelow n :=
  fun hn => (lt_of_mem_primesBelow hn).false

/--
lemma `notMem_primesLE` / 引理 `notMem_primesLE`

English:
lemma notMem_primesLE
  given: (n : Nat)
  statement: n + 1 ∉ primesLE n
  proof: notMem_primesBelow (n + 1)

中文:
引理 notMem_primesLE
  条件: (n : 自然数)
  结论: n + 1 ∉ primesLE n
  证明: notMem_primesBelow (n + 1)

Depends on / 依赖: notMem_primesBelow
-/
lemma notMem_primesLE (n : Nat) : n + 1 ∉ primesLE n :=
  notMem_primesBelow (n + 1)

end PrimeSets

/--
theorem `primesBelow_card_eq_primeCounting'` / 定理 `primesBelow_card_eq_primeCounting'`

English:
theorem primesBelow_card_eq_primeCounting'
  given: (n : Nat)
  statement: #n.primesBelow = π' n
  proof: by
  simp only [primesBelow, primeCounting']
  exact (count_eq_card_filter_range Prime n).symm

中文:
定理 primesBelow_card_eq_primeCounting'
  条件: (n : 自然数)
  结论: #n.primesBelow = π' n
  证明: by
  simp only [primesBelow, primeCounting']
  exact (count_eq_card_filter_range Prime n).symm

Depends on / 依赖: count_eq_card_filter_range, primeCounting, primesBelow
-/
theorem primesBelow_card_eq_primeCounting' (n : Nat) : #n.primesBelow = π' n := by
  simp only [primesBelow, primeCounting']
  exact (count_eq_card_filter_range Prime n).symm

/-- The cardinality of the finset `primesLE n` equals the counting function
`primeCounting` at `n`. -/
@[simp]
/--
theorem `primesLE_card_eq_primeCounting` / 定理 `primesLE_card_eq_primeCounting`

English:
theorem primesLE_card_eq_primeCounting
  given: (n : Nat)
  statement: #(primesLE n) = π n
  proof: by
  simp only [primesLE, primeCounting, primesBelow_card_eq_primeCounting']

中文:
定理 primesLE_card_eq_primeCounting
  条件: (n : 自然数)
  结论: #(primesLE n) = π n
  证明: by
  simp only [primesLE, primeCounting, primesBelow_card_eq_primeCounting']

Depends on / 依赖: primeCounting, primesBelow_card_eq_primeCounting, primesLE
-/
theorem primesLE_card_eq_primeCounting (n : Nat) : #(primesLE n) = π n := by
  simp only [primesLE, primeCounting, primesBelow_card_eq_primeCounting']

/--
theorem `primeCounting'_add_le` / 定理 `primeCounting'_add_le`

English:
theorem primeCounting'_add_le
  given: {a k : Nat} (h0 : a != 0) (h1 : a < k) (n : Nat)
  proof: calc
    π' (k + n) <= #{p in range k | p.Prime} + #{p in Ico k (k + n) | p.Prime} := by
      rw [primeCounting']; rw [count_eq_card_filter_range]; rw [range_eq_Ico]; rw [range_eq_Ico]; rw [←
        Ico_union_Ico_eq_Ico (zero_le k) le_self_add]; rw [filter_union]
      apply card_union_le
    _ <= π' k + #{p in Ico k (k + n) | p.Prime} := by
      rw [primeCounting']; rw [count_eq_card_filter_range]
    _ <= π' k + #{b in Ico k (k + n) | a.Coprime b} := by
      gcongr with p hp
      rw [coprime_comm]
exact coprime_of_lt_prime h0 h1.trans_le (mem_Ico.1 hp).1
    _ <= π' k + totient a * (n / a + 1) := by
      rw [add_le_add_iff_left]
      exact Ico_filter_coprime_le k n h0

中文:
定理 primeCounting'_add_le
  条件: {a k : 自然数} (h0 : a != 0) (h1 : a < k) (n : 自然数)
  证明: calc
    π' (k + n) <= #{p in range k | p.Prime} + #{p in Ico k (k + n) | p.Prime} := by
      rw [primeCounting']; rw [count_eq_card_filter_range]; rw [range_eq_Ico]; rw [range_eq_Ico]; rw [←
        Ico_union_Ico_eq_Ico (zero_le k) le_self_add]; rw [filter_union]
      apply card_union_le
    _ <= π' k + #{p in Ico k (k + n) | p.Prime} := by
      rw [primeCounting']; rw [count_eq_card_filter_range]
    _ <= π' k + #{b in Ico k (k + n) | a.Coprime b} := by
      gcongr with p hp
      rw [coprime_comm]
exact coprime_of_lt_prime h0 h1.trans_le (mem_Ico.1 hp).1
    _ <= π' k + totient a * (n / a + 1) := by
      rw [add_le_add_iff_left]
      exact Ico_filter_coprime_le k n h0
-/
theorem primeCounting'_add_le {a k : Nat} (h0 : a != 0) (h1 : a < k) (n : Nat) :
    π' (k + n) <= π' k + Nat.totient a * (n / a + 1) :=
  calc
    π' (k + n) <= #{p in range k | p.Prime} + #{p in Ico k (k + n) | p.Prime} := by
      rw [primeCounting']; rw [count_eq_card_filter_range]; rw [range_eq_Ico]; rw [range_eq_Ico]; rw [←
        Ico_union_Ico_eq_Ico (zero_le k) le_self_add]; rw [filter_union]
      apply card_union_le
    _ <= π' k + #{p in Ico k (k + n) | p.Prime} := by
      rw [primeCounting']; rw [count_eq_card_filter_range]
    _ <= π' k + #{b in Ico k (k + n) | a.Coprime b} := by
      gcongr with p hp
      rw [coprime_comm]
exact coprime_of_lt_prime h0 h1.trans_le (mem_Ico.1 hp).1
    _ <= π' k + totient a * (n / a + 1) := by
      rw [add_le_add_iff_left]
      exact Ico_filter_coprime_le k n h0

/--
theorem `primeCounting_add_le` / 定理 `primeCounting_add_le`

English:
theorem primeCounting_add_le
  given: {a k : Nat} (h0 : a != 0) (h1 : a <= k) (n : Nat)
  proof: by
  rw [primeCounting_eq_primeCounting'_succ]
  convert! primeCounting'_add_le h0 (Order.lt_add_one_iff.mpr h1) n using 2
  omega

中文:
定理 primeCounting_add_le
  条件: {a k : 自然数} (h0 : a != 0) (h1 : a <= k) (n : 自然数)
  证明: by
  rw [primeCounting_eq_primeCounting'_succ]
  convert! primeCounting'_add_le h0 (Order.lt_add_one_iff.mpr h1) n using 2
  omega

Depends on / 依赖: Order.lt_add_one_iff.mpr, _add_le, _succ, convert, lt_add_one_iff, primeCounting, primeCounting_eq_primeCounting
-/
theorem primeCounting_add_le {a k : Nat} (h0 : a != 0) (h1 : a <= k) (n : Nat) :
    π (k + n) <= π k + totient a * (n / a + 1) := by
  rw [primeCounting_eq_primeCounting'_succ]
  convert! primeCounting'_add_le h0 (Order.lt_add_one_iff.mpr h1) n using 2
  omega

end Nat
