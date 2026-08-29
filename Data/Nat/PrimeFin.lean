/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.Nat.Factors
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Prime numbers

This file contains some results about prime numbers which depend on finiteness of sets.
-/

@[expose] public section

open Finset

namespace Nat
variable {a b k m n p : Nat}

/--
theorem `infinite_setOfPred_prime` / 定理 `infinite_setOfPred_prime`

English:
theorem infinite_setOfPred_prime
  statement: { p | Prime p }.Infinite
  proof: Set.infinite_of_not_bddAbove not_bddAbove_setOfPred_prime

@[deprecated (since := "2026-07-09")] alias infinite_setOf_prime := infinite_setOfPred_prime

中文:
定理 infinite_setOfPred_prime
  结论: { p | Prime p }.Infinite
  证明: Set.infinite_of_not_bddAbove not_bddAbove_setOfPred_prime

@[deprecated (since := "2026-07-09")] alias infinite_setOf_prime := infinite_setOfPred_prime

Depends on / 依赖: Set.infinite_of_not_bddAbove, infinite_of_not_bddAbove, not_bddAbove_setOfPred_prime
-/
theorem infinite_setOfPred_prime : { p | Prime p }.Infinite :=
  Set.infinite_of_not_bddAbove not_bddAbove_setOfPred_prime

@[deprecated (since := "2026-07-09")] alias infinite_setOf_prime := infinite_setOfPred_prime

/--
Instance `Primes.infinite` / 实例 `Primes.infinite`

English:
instance Primes.infinite
  signature: : Infinite Primes
  body: infinite_setOfPred_prime.to_subtype

中文:
实例 Primes.infinite
  签名: : Infinite Primes
  定义体: infinite_setOfPred_prime.to_subtype

Depends on / 依赖: infinite_setOfPred_prime, infinite_setOfPred_prime.to_subtype, to_subtype
-/
instance Primes.infinite : Infinite Primes := infinite_setOfPred_prime.to_subtype

/--
Instance `Primes.countable` / 实例 `Primes.countable`

English:
instance Primes.countable
  signature: : Countable Primes
  body: ⟨⟨coeNat.coe, coe_nat_injective⟩⟩

中文:
实例 Primes.countable
  签名: : Countable Primes
  定义体: ⟨⟨coeNat.coe, coe_nat_injective⟩⟩

Depends on / 依赖: coeNat, coeNat.coe, coe_nat_injective
-/
instance Primes.countable : Countable Primes := ⟨⟨coeNat.coe, coe_nat_injective⟩⟩

/--
Definition of `primeFactors` / `primeFactors` 的定义

English:
definition primeFactors
  signature: (n : Nat)
  body: n.primeFactorsList.toFinset

中文:
定义 primeFactors
  签名: (n : 自然数)
  定义体: n.primeFactorsList.toFinset

Depends on / 依赖: n.primeFactorsList.toFinset, primeFactorsList, toFinset
-/
def primeFactors (n : Nat) : Finset Nat := n.primeFactorsList.toFinset

/--
lemma `toFinset_factors` / 引理 `toFinset_factors`

English:
lemma toFinset_factors
  given: (n : Nat)
  statement: n.primeFactorsList.toFinset = n.primeFactors
  proof: rfl

中文:
引理 toFinset_factors
  条件: (n : 自然数)
  结论: n.primeFactorsList.toFinset = n.primeFactors
  证明: rfl
-/
@[simp] lemma toFinset_factors (n : Nat) : n.primeFactorsList.toFinset = n.primeFactors := rfl

/--
lemma `mem_primeFactors` / 引理 `mem_primeFactors`

English:
lemma mem_primeFactors
  statement: p in n.primeFactors ↔ p.Prime ∧ p ∣ n ∧ n != 0
  proof: by
  simp_rw [← toFinset_factors, List.mem_toFinset, mem_primeFactorsList']

中文:
引理 mem_primeFactors
  结论: p in n.primeFactors ↔ p.Prime ∧ p ∣ n ∧ n != 0
  证明: by
  simp_rw [← toFinset_factors, List.mem_toFinset, mem_primeFactorsList']
-/
@[simp, grind =] lemma mem_primeFactors : p in n.primeFactors ↔ p.Prime ∧ p ∣ n ∧ n != 0 := by
  simp_rw [← toFinset_factors, List.mem_toFinset, mem_primeFactorsList']

/--
lemma `mem_primeFactors_of_ne_zero` / 引理 `mem_primeFactors_of_ne_zero`

English:
lemma mem_primeFactors_of_ne_zero
  given: (hn : n != 0)
  statement: p in n.primeFactors ↔ p.Prime ∧ p ∣ n
  proof: by
  simp [hn]

中文:
引理 mem_primeFactors_of_ne_zero
  条件: (hn : n != 0)
  结论: p in n.primeFactors ↔ p.Prime ∧ p ∣ n
  证明: by
  simp [hn]
-/
lemma mem_primeFactors_of_ne_zero (hn : n != 0) : p in n.primeFactors ↔ p.Prime ∧ p ∣ n := by
  simp [hn]

/--
lemma `Prime.mem_primeFactors` / 引理 `Prime.mem_primeFactors`

English:
lemma Prime.mem_primeFactors
  given: (hp : p.Prime) (hdvd : p ∣ n) (hn : n != 0)
  statement: p in n.primeFactors
  proof: Nat.mem_primeFactors.mpr ⟨hp, hdvd, hn⟩

中文:
引理 Prime.mem_primeFactors
  条件: (hp : p.Prime) (hdvd : p ∣ n) (hn : n != 0)
  结论: p in n.primeFactors
  证明: Nat.mem_primeFactors.mpr ⟨hp, hdvd, hn⟩

Depends on / 依赖: Nat.mem_primeFactors.mpr, mem_primeFactors
-/
lemma Prime.mem_primeFactors (hp : p.Prime) (hdvd : p ∣ n) (hn : n != 0) : p in n.primeFactors :=
  Nat.mem_primeFactors.mpr ⟨hp, hdvd, hn⟩

/--
lemma `Prime.mem_primeFactors'` / 引理 `Prime.mem_primeFactors'`

English:
lemma Prime.mem_primeFactors'
  given: (hp : p.Prime) (hdvd : p ∣ n) [NeZero n]
  statement: p in n.primeFactors
  proof: hp.mem_primeFactors hdvd (NeZero.ne n)

中文:
引理 Prime.mem_primeFactors'
  条件: (hp : p.Prime) (hdvd : p ∣ n) [NeZero n]
  结论: p in n.primeFactors
  证明: hp.mem_primeFactors hdvd (NeZero.ne n)

Depends on / 依赖: NeZero, NeZero.ne, hp.mem_primeFactors, mem_primeFactors
-/
lemma Prime.mem_primeFactors' (hp : p.Prime) (hdvd : p ∣ n) [NeZero n] : p in n.primeFactors :=
  hp.mem_primeFactors hdvd (NeZero.ne n)

/--
lemma `Prime.mem_primeFactors_self` / 引理 `Prime.mem_primeFactors_self`

English:
lemma Prime.mem_primeFactors_self
  given: (hp : p.Prime)
  statement: p in p.primeFactors
  proof: hp.mem_primeFactors p.dvd_refl hp.ne_zero

中文:
引理 Prime.mem_primeFactors_self
  条件: (hp : p.Prime)
  结论: p in p.primeFactors
  证明: hp.mem_primeFactors p.dvd_refl hp.ne_zero

Depends on / 依赖: dvd_refl, hp.mem_primeFactors, hp.ne_zero, mem_primeFactors, ne_zero, p.dvd_refl
-/
lemma Prime.mem_primeFactors_self (hp : p.Prime) : p in p.primeFactors :=
  hp.mem_primeFactors p.dvd_refl hp.ne_zero

/--
lemma `primeFactors_mono` / 引理 `primeFactors_mono`

English:
lemma primeFactors_mono
  given: (hmn : m ∣ n) (hn : n != 0)
  statement: primeFactors m subseteq primeFactors n
  proof: by
  simp only [subset_iff, mem_primeFactors, and_imp]
  exact fun p hp hpm _ => ⟨hp, hpm.trans hmn, hn⟩

中文:
引理 primeFactors_mono
  条件: (hmn : m ∣ n) (hn : n != 0)
  结论: primeFactors m subseteq primeFactors n
  证明: by
  simp only [subset_iff, mem_primeFactors, and_imp]
  exact fun p hp hpm _ => ⟨hp, hpm.trans hmn, hn⟩

Depends on / 依赖: and_imp, hpm.trans, mem_primeFactors, subset_iff
-/
lemma primeFactors_mono (hmn : m ∣ n) (hn : n != 0) : primeFactors m subseteq primeFactors n := by
  simp only [subset_iff, mem_primeFactors, and_imp]
  exact fun p hp hpm _ => ⟨hp, hpm.trans hmn, hn⟩

/--
lemma `mem_primeFactors_iff_mem_primeFactorsList` / 引理 `mem_primeFactors_iff_mem_primeFactorsList`

English:
lemma mem_primeFactors_iff_mem_primeFactorsList
  statement: p in n.primeFactors ↔ p in n.primeFactorsList
  proof: by
  simp only [primeFactors, List.mem_toFinset]

中文:
引理 mem_primeFactors_iff_mem_primeFactorsList
  结论: p in n.primeFactors ↔ p in n.primeFactorsList
  证明: by
  simp only [primeFactors, List.mem_toFinset]

Depends on / 依赖: List.mem_toFinset, mem_toFinset, primeFactors
-/
lemma mem_primeFactors_iff_mem_primeFactorsList : p in n.primeFactors ↔ p in n.primeFactorsList := by
  simp only [primeFactors, List.mem_toFinset]

/--
lemma `prime_of_mem_primeFactors` / 引理 `prime_of_mem_primeFactors`

English:
lemma prime_of_mem_primeFactors
  given: (hp : p in n.primeFactors)
  statement: p.Prime
  proof: (mem_primeFactors.1 hp).1

中文:
引理 prime_of_mem_primeFactors
  条件: (hp : p in n.primeFactors)
  结论: p.Prime
  证明: (mem_primeFactors.1 hp).1

Depends on / 依赖: mem_primeFactors
-/
lemma prime_of_mem_primeFactors (hp : p in n.primeFactors) : p.Prime := (mem_primeFactors.1 hp).1
/--
lemma `dvd_of_mem_primeFactors` / 引理 `dvd_of_mem_primeFactors`

English:
lemma dvd_of_mem_primeFactors
  given: (hp : p in n.primeFactors)
  statement: p ∣ n
  proof: (mem_primeFactors.1 hp).2.1

中文:
引理 dvd_of_mem_primeFactors
  条件: (hp : p in n.primeFactors)
  结论: p ∣ n
  证明: (mem_primeFactors.1 hp).2.1

Depends on / 依赖: mem_primeFactors
-/
lemma dvd_of_mem_primeFactors (hp : p in n.primeFactors) : p ∣ n := (mem_primeFactors.1 hp).2.1

/--
lemma `pos_of_mem_primeFactors` / 引理 `pos_of_mem_primeFactors`

English:
lemma pos_of_mem_primeFactors
  given: (hp : p in n.primeFactors)
  statement: 0 < p
  proof: (prime_of_mem_primeFactors hp).pos

中文:
引理 pos_of_mem_primeFactors
  条件: (hp : p in n.primeFactors)
  结论: 0 < p
  证明: (prime_of_mem_primeFactors hp).pos

Depends on / 依赖: prime_of_mem_primeFactors
-/
lemma pos_of_mem_primeFactors (hp : p in n.primeFactors) : 0 < p :=
  (prime_of_mem_primeFactors hp).pos

/--
lemma `le_of_mem_primeFactors` / 引理 `le_of_mem_primeFactors`

English:
lemma le_of_mem_primeFactors
  given: (h : p in n.primeFactors)
  statement: p <= n
  proof: le_of_dvd (mem_primeFactors.1 h).2.2.bot_lt dvd_of_mem_primeFactors h

中文:
引理 le_of_mem_primeFactors
  条件: (h : p in n.primeFactors)
  结论: p <= n
  证明: le_of_dvd (mem_primeFactors.1 h).2.2.bot_lt dvd_of_mem_primeFactors h

Depends on / 依赖: bot_lt, dvd_of_mem_primeFactors, le_of_dvd, mem_primeFactors
-/
lemma le_of_mem_primeFactors (h : p in n.primeFactors) : p <= n :=
le_of_dvd (mem_primeFactors.1 h).2.2.bot_lt dvd_of_mem_primeFactors h

/--
lemma `primeFactors_zero` / 引理 `primeFactors_zero`

English:
lemma primeFactors_zero
  statement: primeFactors 0 = ∅
  proof: by
  ext
  simp

中文:
引理 primeFactors_zero
  结论: primeFactors 0 = ∅
  证明: by
  ext
  simp
-/
@[simp] lemma primeFactors_zero : primeFactors 0 = ∅ := by
  ext
  simp

/--
lemma `primeFactors_one` / 引理 `primeFactors_one`

English:
lemma primeFactors_one
  statement: primeFactors 1 = ∅
  proof: by
  ext
  simpa using Prime.ne_one

中文:
引理 primeFactors_one
  结论: primeFactors 1 = ∅
  证明: by
  ext
  simpa using Prime.ne_one
-/
@[simp] lemma primeFactors_one : primeFactors 1 = ∅ := by
  ext
  simpa using Prime.ne_one

/--
lemma `primeFactors_eq_empty` / 引理 `primeFactors_eq_empty`

English:
lemma primeFactors_eq_empty
  statement: n.primeFactors = ∅ ↔ n = 0 ∨ n = 1
  proof: by
  constructor
  · contrapose!
    rintro hn
    obtain ⟨p, hp, hpn⟩ := exists_prime_and_dvd hn.2
    exact ⟨_, mem_primeFactors.2 ⟨hp, hpn, hn.1⟩⟩
  · rintro (rfl | rfl) <;> simp

@[simp]

中文:
引理 primeFactors_eq_empty
  结论: n.primeFactors = ∅ ↔ n = 0 ∨ n = 1
  证明: by
  constructor
  · contrapose!
    rintro hn
    obtain ⟨p, hp, hpn⟩ := exists_prime_and_dvd hn.2
    exact ⟨_, mem_primeFactors.2 ⟨hp, hpn, hn.1⟩⟩
  · rintro (rfl | rfl) <;> simp

@[simp]
-/
@[simp] lemma primeFactors_eq_empty : n.primeFactors = ∅ ↔ n = 0 ∨ n = 1 := by
  constructor
  · contrapose!
    rintro hn
    obtain ⟨p, hp, hpn⟩ := exists_prime_and_dvd hn.2
    exact ⟨_, mem_primeFactors.2 ⟨hp, hpn, hn.1⟩⟩
  · rintro (rfl | rfl) <;> simp

@[simp]
/--
lemma `nonempty_primeFactors` / 引理 `nonempty_primeFactors`

English:
lemma nonempty_primeFactors
  given: {n : Nat}
  statement: n.primeFactors.Nonempty ↔ 1 < n
  proof: by
  contrapose!
  rw [primeFactors_eq_empty]; rw [Nat.le_one_iff_eq_zero_or_eq_one]

中文:
引理 nonempty_primeFactors
  条件: {n : 自然数}
  结论: n.primeFactors.Nonempty ↔ 1 < n
  证明: by
  contrapose!
  rw [primeFactors_eq_empty]; rw [Nat.le_one_iff_eq_zero_or_eq_one]

Depends on / 依赖: Nat.le_one_iff_eq_zero_or_eq_one, contrapose, le_one_iff_eq_zero_or_eq_one, primeFactors_eq_empty
-/
lemma nonempty_primeFactors {n : Nat} : n.primeFactors.Nonempty ↔ 1 < n := by
  contrapose!
  rw [primeFactors_eq_empty]; rw [Nat.le_one_iff_eq_zero_or_eq_one]

/--
lemma `Prime.primeFactors` / 引理 `Prime.primeFactors`

English:
lemma Prime.primeFactors
  given: (hp : p.Prime)
  statement: p.primeFactors = {p}
  proof: by
  simp [Nat.primeFactors, primeFactorsList_prime hp]

中文:
引理 Prime.primeFactors
  条件: (hp : p.Prime)
  结论: p.primeFactors = {p}
  证明: by
  simp [Nat.primeFactors, primeFactorsList_prime hp]
-/
@[simp] protected lemma Prime.primeFactors (hp : p.Prime) : p.primeFactors = {p} := by
  simp [Nat.primeFactors, primeFactorsList_prime hp]

/--
lemma `primeFactors_mul` / 引理 `primeFactors_mul`

English:
lemma primeFactors_mul
  given: (ha : a != 0) (hb : b != 0)
  proof: by
  ext; simp only [Finset.mem_union, mem_primeFactors_iff_mem_primeFactorsList,
    mem_primeFactorsList_mul ha hb]

中文:
引理 primeFactors_mul
  条件: (ha : a != 0) (hb : b != 0)
  证明: by
  ext; simp only [Finset.mem_union, mem_primeFactors_iff_mem_primeFactorsList,
    mem_primeFactorsList_mul ha hb]

Depends on / 依赖: Finset, Finset.mem_union, mem_primeFactorsList_mul, mem_primeFactors_iff_mem_primeFactorsList, mem_union
-/
lemma primeFactors_mul (ha : a != 0) (hb : b != 0) :
    (a * b).primeFactors = a.primeFactors union b.primeFactors := by
  ext; simp only [Finset.mem_union, mem_primeFactors_iff_mem_primeFactorsList,
    mem_primeFactorsList_mul ha hb]

/--
lemma `Coprime.primeFactors_mul` / 引理 `Coprime.primeFactors_mul`

English:
lemma Coprime.primeFactors_mul
  given: {a b : Nat} (hab : Coprime a b)
  proof: (List.toFinset.ext <| mem_primeFactorsList_mul_of_coprime hab).trans List.toFinset_union _ _

中文:
引理 Coprime.primeFactors_mul
  条件: {a b : 自然数} (hab : Coprime a b)
  证明: (List.toFinset.ext <| mem_primeFactorsList_mul_of_coprime hab).trans List.toFinset_union _ _

Depends on / 依赖: List.toFinset.ext, List.toFinset_union, mem_primeFactorsList_mul_of_coprime, toFinset, toFinset_union
-/
lemma Coprime.primeFactors_mul {a b : Nat} (hab : Coprime a b) :
    (a * b).primeFactors = a.primeFactors union b.primeFactors :=
(List.toFinset.ext <| mem_primeFactorsList_mul_of_coprime hab).trans List.toFinset_union _ _

/--
lemma `primeFactors_gcd` / 引理 `primeFactors_gcd`

English:
lemma primeFactors_gcd
  given: (ha : a != 0) (hb : b != 0)
  proof: by
  grind [dvd_gcd_iff]

中文:
引理 primeFactors_gcd
  条件: (ha : a != 0) (hb : b != 0)
  证明: by
  grind [dvd_gcd_iff]

Depends on / 依赖: dvd_gcd_iff
-/
lemma primeFactors_gcd (ha : a != 0) (hb : b != 0) :
    (a.gcd b).primeFactors = a.primeFactors inter b.primeFactors := by
  grind [dvd_gcd_iff]

/--
lemma `disjoint_primeFactors` / 引理 `disjoint_primeFactors`

English:
lemma disjoint_primeFactors
  given: (ha : a != 0) (hb : b != 0)
  proof: by
  simp [disjoint_iff_inter_eq_empty, coprime_iff_gcd_eq_one, ← primeFactors_gcd,
    ha, hb]

中文:
引理 disjoint_primeFactors
  条件: (ha : a != 0) (hb : b != 0)
  证明: by
  simp [disjoint_iff_inter_eq_empty, coprime_iff_gcd_eq_one, ← primeFactors_gcd,
    ha, hb]
-/
@[simp] lemma disjoint_primeFactors (ha : a != 0) (hb : b != 0) :
    Disjoint a.primeFactors b.primeFactors ↔ Coprime a b := by
  simp [disjoint_iff_inter_eq_empty, coprime_iff_gcd_eq_one, ← primeFactors_gcd,
    ha, hb]

/--
lemma `Coprime.disjoint_primeFactors` / 引理 `Coprime.disjoint_primeFactors`

English:
lemma Coprime.disjoint_primeFactors
  given: (hab : Coprime a b)
  proof: List.disjoint_toFinset_iff_disjoint.2 coprime_primeFactorsList_disjoint hab

中文:
引理 Coprime.disjoint_primeFactors
  条件: (hab : Coprime a b)
  证明: List.disjoint_toFinset_iff_disjoint.2 coprime_primeFactorsList_disjoint hab
-/
protected lemma Coprime.disjoint_primeFactors (hab : Coprime a b) :
    Disjoint a.primeFactors b.primeFactors :=
List.disjoint_toFinset_iff_disjoint.2 coprime_primeFactorsList_disjoint hab

/--
lemma `primeFactors_pow_succ` / 引理 `primeFactors_pow_succ`

English:
lemma primeFactors_pow_succ
  given: (n k : Nat)
  statement: (n ^ (k + 1)).primeFactors = n.primeFactors
  proof: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', primeFactors_mul hn (pow_ne_zero _ hn), ih, Finset.union_idempotent]

中文:
引理 primeFactors_pow_succ
  条件: (n k : 自然数)
  结论: (n ^ (k + 1)).primeFactors = n.primeFactors
  证明: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', primeFactors_mul hn (pow_ne_zero _ hn), ih, Finset.union_idempotent]

Depends on / 依赖: Finset, Finset.union_idempotent, eq_or_ne, pow_ne_zero, pow_succ, primeFactors_mul, union_idempotent
-/
lemma primeFactors_pow_succ (n k : Nat) : (n ^ (k + 1)).primeFactors = n.primeFactors := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', primeFactors_mul hn (pow_ne_zero _ hn), ih, Finset.union_idempotent]

/--
lemma `primeFactors_pow` / 引理 `primeFactors_pow`

English:
lemma primeFactors_pow
  given: (n : Nat) (hk : k != 0)
  statement: (n ^ k).primeFactors = n.primeFactors
  proof: by
  cases k
  · simp at hk
  rw [primeFactors_pow_succ]

中文:
引理 primeFactors_pow
  条件: (n : 自然数) (hk : k != 0)
  结论: (n ^ k).primeFactors = n.primeFactors
  证明: by
  cases k
  · simp at hk
  rw [primeFactors_pow_succ]

Depends on / 依赖: primeFactors_pow_succ
-/
lemma primeFactors_pow (n : Nat) (hk : k != 0) : (n ^ k).primeFactors = n.primeFactors := by
  cases k
  · simp at hk
  rw [primeFactors_pow_succ]

/--
lemma `primeFactors_prime_pow` / 引理 `primeFactors_prime_pow`

English:
lemma primeFactors_prime_pow
  given: (hk : k != 0) (hp : Prime p)
  proof: by simp [primeFactors_pow p hk, hp]

中文:
引理 primeFactors_prime_pow
  条件: (hk : k != 0) (hp : Prime p)
  证明: by simp [primeFactors_pow p hk, hp]

Depends on / 依赖: primeFactors_pow
-/
lemma primeFactors_prime_pow (hk : k != 0) (hp : Prime p) :
    (p ^ k).primeFactors = {p} := by simp [primeFactors_pow p hk, hp]

end Nat
