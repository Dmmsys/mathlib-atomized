/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.List.Prime
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Perm.Subperm

/-!
# Prime numbers

This file deals with the factors of natural numbers.

## Important declarations

- `Nat.primeFactorsList n`: the prime factorization of `n`
- `Nat.primeFactorsList_unique`: uniqueness of the prime factorisation

-/

@[expose] public section

assert_not_exists Multiset

open Bool Subtype

open Nat

namespace Nat

/--
Definition of `primeFactorsList` / `primeFactorsList` 的定义

English:
definition primeFactorsList
  signature: : Nat -> List Nat
  body: minFac (k + 2)
    m :: primeFactorsList ((k + 2) / m)
decreasing_by exact factors_lemma

@[simp]

中文:
定义 primeFactorsList
  签名: : 自然数 -> 列表 自然数
  定义体: minFac (k + 2)
    m :: primeFactorsList ((k + 2) / m)
decreasing_by exact factors_lemma

@[simp]

Depends on / 依赖: minFac
-/
def primeFactorsList : Nat -> List Nat
  | 0 => []
  | 1 => []
  | k + 2 =>
    let m := minFac (k + 2)
    m :: primeFactorsList ((k + 2) / m)
decreasing_by exact factors_lemma

@[simp]
/--
theorem `primeFactorsList_zero` / 定理 `primeFactorsList_zero`

English:
theorem primeFactorsList_zero
  statement: primeFactorsList 0 = []
  proof: by rw [primeFactorsList]

@[simp]

中文:
定理 primeFactorsList_zero
  结论: primeFactorsList 0 = []
  证明: by rw [primeFactorsList]

@[simp]

Depends on / 依赖: primeFactorsList
-/
theorem primeFactorsList_zero : primeFactorsList 0 = [] := by rw [primeFactorsList]

@[simp]
/--
theorem `primeFactorsList_one` / 定理 `primeFactorsList_one`

English:
theorem primeFactorsList_one
  statement: primeFactorsList 1 = []
  proof: by rw [primeFactorsList]

@[simp]

中文:
定理 primeFactorsList_one
  结论: primeFactorsList 1 = []
  证明: by rw [primeFactorsList]

@[simp]

Depends on / 依赖: primeFactorsList
-/
theorem primeFactorsList_one : primeFactorsList 1 = [] := by rw [primeFactorsList]

@[simp]
/--
theorem `primeFactorsList_two` / 定理 `primeFactorsList_two`

English:
theorem primeFactorsList_two
  statement: primeFactorsList 2 = [2]
  proof: by simp [primeFactorsList]

中文:
定理 primeFactorsList_two
  结论: primeFactorsList 2 = [2]
  证明: by simp [primeFactorsList]

Depends on / 依赖: primeFactorsList
-/
theorem primeFactorsList_two : primeFactorsList 2 = [2] := by simp [primeFactorsList]

/--
theorem `prime_of_mem_primeFactorsList` / 定理 `prime_of_mem_primeFactorsList`

English:
theorem prime_of_mem_primeFactorsList
  given: {n : Nat}
  statement: forall {p : Nat}, p in primeFactorsList n -> Prime p
  proof: by
  match n with
  | 0 => simp
  | 1 => simp
  | k + 2 =>
      intro p h
      let m := minFac (k + 2)
      have : (k + 2) / m < (k + 2) := factors_lemma
      have h₁ : p = m ∨ p in primeFactorsList ((k + 2) / m) :=
        List.mem_cons.1 (by rwa [primeFactorsList] at h)
      exact Or.casesOn 

中文:
定理 prime_of_mem_primeFactorsList
  条件: {n : 自然数}
  结论: 对任意 {p : 自然数}, p in primeFactorsList n -> 素 p
  证明: by
  match n with
  | 0 => simp
  | 1 => simp
  | k + 2 =>
      intro p h
      let m := minFac (k + 2)
      have : (k + 2) / m < (k + 2) := factors_lemma
      have h₁ : p = m ∨ p in primeFactorsList ((k + 2) / m) :=
        List.mem_cons.1 (by rwa [primeFactorsList] at h)
      exact Or.casesOn 

Depends on / 依赖: List.mem_cons, Or.casesOn, casesOn, factors_lemma, mem_cons, minFac, minFac_prime, primeFactorsList, prime_of_mem_primeFactorsList
-/
theorem prime_of_mem_primeFactorsList {n : Nat} : forall {p : Nat}, p in primeFactorsList n -> Prime p := by
  match n with
  | 0 => simp
  | 1 => simp
  | k + 2 =>
      intro p h
      let m := minFac (k + 2)
      have : (k + 2) / m < (k + 2) := factors_lemma
      have h₁ : p = m ∨ p in primeFactorsList ((k + 2) / m) :=
        List.mem_cons.1 (by rwa [primeFactorsList] at h)
      exact Or.casesOn h₁ (fun h₂ => h₂.symm ▸ minFac_prime (by simp)) prime_of_mem_primeFactorsList

/--
theorem `pos_of_mem_primeFactorsList` / 定理 `pos_of_mem_primeFactorsList`

English:
theorem pos_of_mem_primeFactorsList
  given: {n p : Nat} (h : p in primeFactorsList n)
  statement: 0 < p
  proof: Prime.pos (prime_of_mem_primeFactorsList h)

中文:
定理 pos_of_mem_primeFactorsList
  条件: {n p : 自然数} (h : p in primeFactorsList n)
  结论: 0 < p
  证明: Prime.pos (prime_of_mem_primeFactorsList h)

Depends on / 依赖: Prime.pos, prime_of_mem_primeFactorsList
-/
theorem pos_of_mem_primeFactorsList {n p : Nat} (h : p in primeFactorsList n) : 0 < p :=
  Prime.pos (prime_of_mem_primeFactorsList h)

/--
theorem `prod_primeFactorsList` / 定理 `prod_primeFactorsList`

English:
theorem prod_primeFactorsList
  statement: forall {n}, n != 0 -> List.prod (primeFactorsList n) = n
  proof: minFac (k + 2)
    have : (k + 2) / m < (k + 2) := factors_lemma
    show (primeFactorsList (k + 2)).prod = (k + 2) by
      have h₁ : (k + 2) / m != 0 := fun h => by
        have : (k + 2) = 0 * m := (Nat.div_eq_iff_eq_mul_left (minFac_pos _) (minFac_dvd _)).1 h
        rw [zero_mul] at this; exact

中文:
定理 prod_primeFactorsList
  结论: 对任意 {n}, n != 0 -> 列表.乘积 (primeFactorsList n) = n
  证明: minFac (k + 2)
    have : (k + 2) / m < (k + 2) := factors_lemma
    show (primeFactorsList (k + 2)).prod = (k + 2) by
      have h₁ : (k + 2) / m != 0 := fun h => by
        have : (k + 2) = 0 * m := (Nat.div_eq_iff_eq_mul_left (minFac_pos _) (minFac_dvd _)).1 h
        rw [zero_mul] at this; exact

Depends on / 依赖: minFac
-/
theorem prod_primeFactorsList : forall {n}, n != 0 -> List.prod (primeFactorsList n) = n
  | 0 => by simp
  | 1 => by simp
  | k + 2 => fun _ =>
    let m := minFac (k + 2)
    have : (k + 2) / m < (k + 2) := factors_lemma
    show (primeFactorsList (k + 2)).prod = (k + 2) by
      have h₁ : (k + 2) / m != 0 := fun h => by
        have : (k + 2) = 0 * m := (Nat.div_eq_iff_eq_mul_left (minFac_pos _) (minFac_dvd _)).1 h
        rw [zero_mul] at this; exact (show k + 2 != 0 by simp) this
      rw [primeFactorsList]; rw [List.prod_cons]; rw [prod_primeFactorsList h₁]; rw [Nat.mul_div_cancel' (minFac_dvd _)]

/--
theorem `primeFactorsList_prime` / 定理 `primeFactorsList_prime`

English:
theorem primeFactorsList_prime
  given: {p : Nat} (hp : Nat.Prime p)
  statement: p.primeFactorsList = [p]
  proof: by
  have : p = p - 2 + 2 := Nat.eq_add_of_sub_eq hp.two_le rfl
  rw [this]; rw [primeFactorsList]
  simp only [Eq.symm this]
  have : Nat.minFac p = p := (Nat.prime_def_minFac.mp hp).2
  simp only [this, primeFactorsList, Nat.div_self (Nat.Prime.pos hp)]

中文:
定理 primeFactorsList_prime
  条件: {p : 自然数} (hp : 自然数.素 p)
  结论: p.primeFactorsList = [p]
  证明: by
  have : p = p - 2 + 2 := Nat.eq_add_of_sub_eq hp.two_le rfl
  rw [this]; rw [primeFactorsList]
  simp only [Eq.symm this]
  have : Nat.minFac p = p := (Nat.prime_def_minFac.mp hp).2
  simp only [this, primeFactorsList, Nat.div_self (Nat.Prime.pos hp)]

Depends on / 依赖: Eq.symm, Nat.Prime.pos, Nat.div_self, Nat.eq_add_of_sub_eq, Nat.minFac, Nat.prime_def_minFac.mp, div_self, eq_add_of_sub_eq, hp.two_le, minFac, primeFactorsList, prime_def_minFac, two_le
-/
theorem primeFactorsList_prime {p : Nat} (hp : Nat.Prime p) : p.primeFactorsList = [p] := by
  have : p = p - 2 + 2 := Nat.eq_add_of_sub_eq hp.two_le rfl
  rw [this]; rw [primeFactorsList]
  simp only [Eq.symm this]
  have : Nat.minFac p = p := (Nat.prime_def_minFac.mp hp).2
  simp only [this, primeFactorsList, Nat.div_self (Nat.Prime.pos hp)]

/--
theorem `isChain_cons_primeFactorsList` / 定理 `isChain_cons_primeFactorsList`

English:
theorem isChain_cons_primeFactorsList
  given: {n : Nat}
  proof: by
  match n with
  | 0 => simp
  | 1 => simp
  | k + 2 =>
      intro a h
      let m := minFac (k + 2)
      have : (k + 2) / m < (k + 2) := factors_lemma
      rw [primeFactorsList]
      refine List.IsChain.cons_cons
        ((le_minFac.2 h).resolve_left (by simp)) (isChain_cons_primeFactorsList

中文:
定理 isChain_cons_primeFactorsList
  条件: {n : 自然数}
  证明: by
  match n with
  | 0 => simp
  | 1 => simp
  | k + 2 =>
      intro a h
      let m := minFac (k + 2)
      have : (k + 2) / m < (k + 2) := factors_lemma
      rw [primeFactorsList]
      refine List.IsChain.cons_cons
        ((le_minFac.2 h).resolve_left (by simp)) (isChain_cons_primeFactorsList

Depends on / 依赖: IsChain, List.IsChain.cons_cons, cons_cons, d.trans, div_dvd_of_dvd, factors_lemma, isChain_cons_primeFactorsList, le_minFac, minFac, minFac_dvd, minFac_le_of_dvd, pp.two_le, primeFactorsList, resolve_left, two_le
-/
theorem isChain_cons_primeFactorsList {n : Nat} :
    forall {a}, (forall p, Prime p -> p ∣ n -> a <= p) -> List.IsChain (· <= ·) (a :: primeFactorsList n) := by
  match n with
  | 0 => simp
  | 1 => simp
  | k + 2 =>
      intro a h
      let m := minFac (k + 2)
      have : (k + 2) / m < (k + 2) := factors_lemma
      rw [primeFactorsList]
      refine List.IsChain.cons_cons
        ((le_minFac.2 h).resolve_left (by simp)) (isChain_cons_primeFactorsList ?_)
      exact fun p pp d => minFac_le_of_dvd pp.two_le (d.trans <| div_dvd_of_dvd <| minFac_dvd _)

/--
theorem `isChain_two_cons_primeFactorsList` / 定理 `isChain_two_cons_primeFactorsList`

English:
theorem isChain_two_cons_primeFactorsList
  given: (n)
  statement: List.IsChain (· <= ·) (2 :: primeFactorsList n)
  proof: isChain_cons_primeFactorsList fun _ pp _ => pp.two_le

中文:
定理 isChain_two_cons_primeFactorsList
  条件: (n)
  结论: 列表.IsChain (· <= ·) (2 :: primeFactorsList n)
  证明: isChain_cons_primeFactorsList fun _ pp _ => pp.two_le

Depends on / 依赖: isChain_cons_primeFactorsList, pp.two_le, two_le
-/
theorem isChain_two_cons_primeFactorsList (n) : List.IsChain (· <= ·) (2 :: primeFactorsList n) :=
  isChain_cons_primeFactorsList fun _ pp _ => pp.two_le

/--
theorem `isChain_primeFactorsList` / 定理 `isChain_primeFactorsList`

English:
theorem isChain_primeFactorsList
  given: (n)
  statement: List.IsChain (· <= ·) (primeFactorsList n)
  proof: (isChain_two_cons_primeFactorsList _).tail

中文:
定理 isChain_primeFactorsList
  条件: (n)
  结论: 列表.IsChain (· <= ·) (primeFactorsList n)
  证明: (isChain_two_cons_primeFactorsList _).tail

Depends on / 依赖: isChain_two_cons_primeFactorsList
-/
theorem isChain_primeFactorsList (n) : List.IsChain (· <= ·) (primeFactorsList n) :=
  (isChain_two_cons_primeFactorsList _).tail

/--
theorem `primeFactorsList_sorted` / 定理 `primeFactorsList_sorted`

English:
theorem primeFactorsList_sorted
  given: (n : Nat)
  statement: List.SortedLE (primeFactorsList n)
  proof: (isChain_primeFactorsList _).sortedLE

中文:
定理 primeFactorsList_sorted
  条件: (n : 自然数)
  结论: 列表.SortedLE (primeFactorsList n)
  证明: (isChain_primeFactorsList _).sortedLE

Depends on / 依赖: isChain_primeFactorsList, sortedLE
-/
theorem primeFactorsList_sorted (n : Nat) : List.SortedLE (primeFactorsList n) :=
  (isChain_primeFactorsList _).sortedLE

/--
theorem `primeFactorsList_add_two` / 定理 `primeFactorsList_add_two`

English:
theorem primeFactorsList_add_two
  given: (n : Nat)
  proof: by
  rw [primeFactorsList]

@[simp]

中文:
定理 primeFactorsList_add_two
  条件: (n : 自然数)
  证明: by
  rw [primeFactorsList]

@[simp]

Depends on / 依赖: primeFactorsList
-/
theorem primeFactorsList_add_two (n : Nat) :
    primeFactorsList (n + 2) = minFac (n + 2) :: primeFactorsList ((n + 2) / minFac (n + 2)) := by
  rw [primeFactorsList]

@[simp]
/--
theorem `primeFactorsList_eq_nil` / 定理 `primeFactorsList_eq_nil`

English:
theorem primeFactorsList_eq_nil
  given: (n : Nat)
  statement: n.primeFactorsList = [] ↔ n = 0 ∨ n = 1
  proof: by
  constructor <;> intro h
  · rcases n with (_ | _ | n)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rw [primeFactorsList] at h
      injection h
  · rcases h with (rfl | rfl)
    · exact primeFactorsList_zero
    · exact primeFactorsList_one

中文:
定理 primeFactorsList_eq_nil
  条件: (n : 自然数)
  结论: n.primeFactorsList = [] ↔ n = 0 ∨ n = 1
  证明: by
  constructor <;> intro h
  · rcases n with (_ | _ | n)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rw [primeFactorsList] at h
      injection h
  · rcases h with (rfl | rfl)
    · exact primeFactorsList_zero
    · exact primeFactorsList_one

Depends on / 依赖: Or.inl, Or.inr, injection, primeFactorsList, primeFactorsList_one, primeFactorsList_zero
-/
theorem primeFactorsList_eq_nil (n : Nat) : n.primeFactorsList = [] ↔ n = 0 ∨ n = 1 := by
  constructor <;> intro h
  · rcases n with (_ | _ | n)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rw [primeFactorsList] at h
      injection h
  · rcases h with (rfl | rfl)
    · exact primeFactorsList_zero
    · exact primeFactorsList_one

/--
theorem `primeFactorsList_ne_nil` / 定理 `primeFactorsList_ne_nil`

English:
theorem primeFactorsList_ne_nil
  given: (n : Nat)
  statement: n.primeFactorsList != [] ↔ 1 < n
  proof: by
  simp [primeFactorsList_eq_nil n, one_lt_iff_ne_zero_and_ne_one]

中文:
定理 primeFactorsList_ne_nil
  条件: (n : 自然数)
  结论: n.primeFactorsList != [] ↔ 1 < n
  证明: by
  simp [primeFactorsList_eq_nil n, one_lt_iff_ne_zero_and_ne_one]

Depends on / 依赖: one_lt_iff_ne_zero_and_ne_one, primeFactorsList_eq_nil
-/
theorem primeFactorsList_ne_nil (n : Nat) : n.primeFactorsList != [] ↔ 1 < n := by
  simp [primeFactorsList_eq_nil n, one_lt_iff_ne_zero_and_ne_one]

open scoped List in
/--
theorem `eq_of_perm_primeFactorsList` / 定理 `eq_of_perm_primeFactorsList`

English:
theorem eq_of_perm_primeFactorsList
  statement: {a b : Nat} (ha : a != 0) (hb : b != 0)
  proof: by
  simpa [prod_primeFactorsList ha, prod_primeFactorsList hb] using List.Perm.prod_eq h

中文:
定理 eq_of_perm_primeFactorsList
  结论: {a b : 自然数} (ha : a != 0) (hb : b != 0)
  证明: by
  simpa [prod_primeFactorsList ha, prod_primeFactorsList hb] using List.Perm.prod_eq h

Depends on / 依赖: List.Perm.prod_eq, prod_eq, prod_primeFactorsList
-/
theorem eq_of_perm_primeFactorsList {a b : Nat} (ha : a != 0) (hb : b != 0)
    (h : a.primeFactorsList ~ b.primeFactorsList) : a = b := by
  simpa [prod_primeFactorsList ha, prod_primeFactorsList hb] using List.Perm.prod_eq h

section

open List

/--
theorem `mem_primeFactorsList_iff_dvd` / 定理 `mem_primeFactorsList_iff_dvd`

English:
theorem mem_primeFactorsList_iff_dvd
  given: {n p : Nat} (hn : n != 0) (hp : Prime p)
  proof: prod_primeFactorsList hn ▸ List.dvd_prod h
  mpr h := mem_list_primes_of_dvd_prod (prime_iff.mp hp)
    (fun _ h => prime_iff.mp (prime_of_mem_primeFactorsList h)) ((prod_primeFactorsList hn).symm ▸ h)

中文:
定理 mem_primeFactorsList_iff_dvd
  条件: {n p : 自然数} (hn : n != 0) (hp : 素 p)
  证明: prod_primeFactorsList hn ▸ List.dvd_prod h
  mpr h := mem_list_primes_of_dvd_prod (prime_iff.mp hp)
    (fun _ h => prime_iff.mp (prime_of_mem_primeFactorsList h)) ((prod_primeFactorsList hn).symm ▸ h)

Depends on / 依赖: List.dvd_prod, dvd_prod, prod_primeFactorsList
-/
theorem mem_primeFactorsList_iff_dvd {n p : Nat} (hn : n != 0) (hp : Prime p) :
    p in primeFactorsList n ↔ p ∣ n where
  mp h := prod_primeFactorsList hn ▸ List.dvd_prod h
  mpr h := mem_list_primes_of_dvd_prod (prime_iff.mp hp)
    (fun _ h => prime_iff.mp (prime_of_mem_primeFactorsList h)) ((prod_primeFactorsList hn).symm ▸ h)

/--
theorem `dvd_of_mem_primeFactorsList` / 定理 `dvd_of_mem_primeFactorsList`

English:
theorem dvd_of_mem_primeFactorsList
  given: {n p : Nat} (h : p in n.primeFactorsList)
  statement: p ∣ n
  proof: by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · exact dvd_zero p
  · rwa [← mem_primeFactorsList_iff_dvd hn.ne' (prime_of_mem_primeFactorsList h)]

中文:
定理 dvd_of_mem_primeFactorsList
  条件: {n p : 自然数} (h : p in n.primeFactorsList)
  结论: p ∣ n
  证明: by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · exact dvd_zero p
  · rwa [← mem_primeFactorsList_iff_dvd hn.ne' (prime_of_mem_primeFactorsList h)]

Depends on / 依赖: dvd_zero, eq_zero_or_pos, hn.ne, mem_primeFactorsList_iff_dvd, n.eq_zero_or_pos, prime_of_mem_primeFactorsList
-/
theorem dvd_of_mem_primeFactorsList {n p : Nat} (h : p in n.primeFactorsList) : p ∣ n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · exact dvd_zero p
  · rwa [← mem_primeFactorsList_iff_dvd hn.ne' (prime_of_mem_primeFactorsList h)]

/--
theorem `mem_primeFactorsList` / 定理 `mem_primeFactorsList`

English:
theorem mem_primeFactorsList
  given: {n p} (hn : n != 0)
  statement: p in primeFactorsList n ↔ Prime p ∧ p ∣ n
  proof: ⟨fun h => ⟨prime_of_mem_primeFactorsList h, dvd_of_mem_primeFactorsList h⟩, fun ⟨hprime, hdvd⟩ =>
    (mem_primeFactorsList_iff_dvd hn hprime).mpr hdvd⟩

中文:
定理 mem_primeFactorsList
  条件: {n p} (hn : n != 0)
  结论: p in primeFactorsList n ↔ 素 p ∧ p ∣ n
  证明: ⟨fun h => ⟨prime_of_mem_primeFactorsList h, dvd_of_mem_primeFactorsList h⟩, fun ⟨hprime, hdvd⟩ =>
    (mem_primeFactorsList_iff_dvd hn hprime).mpr hdvd⟩

Depends on / 依赖: dvd_of_mem_primeFactorsList, hprime, mem_primeFactorsList_iff_dvd, prime_of_mem_primeFactorsList
-/
theorem mem_primeFactorsList {n p} (hn : n != 0) : p in primeFactorsList n ↔ Prime p ∧ p ∣ n :=
  ⟨fun h => ⟨prime_of_mem_primeFactorsList h, dvd_of_mem_primeFactorsList h⟩, fun ⟨hprime, hdvd⟩ =>
    (mem_primeFactorsList_iff_dvd hn hprime).mpr hdvd⟩

/--
lemma `mem_primeFactorsList'` / 引理 `mem_primeFactorsList'`

English:
lemma mem_primeFactorsList'
  given: {n p}
  statement: p in n.primeFactorsList ↔ p.Prime ∧ p ∣ n ∧ n != 0
  proof: by
  cases n <;> simp [mem_primeFactorsList, *]

中文:
引理 mem_primeFactorsList'
  条件: {n p}
  结论: p in n.primeFactorsList ↔ p.素 ∧ p ∣ n ∧ n != 0
  证明: by
  cases n <;> simp [mem_primeFactorsList, *]
-/
@[simp] lemma mem_primeFactorsList' {n p} : p in n.primeFactorsList ↔ p.Prime ∧ p ∣ n ∧ n != 0 := by
  cases n <;> simp [mem_primeFactorsList, *]

/--
theorem `le_of_mem_primeFactorsList` / 定理 `le_of_mem_primeFactorsList`

English:
theorem le_of_mem_primeFactorsList
  given: {n p : Nat} (h : p in n.primeFactorsList)
  statement: p <= n
  proof: by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · rw [primeFactorsList_zero] at h
    cases h
  · exact le_of_dvd hn (dvd_of_mem_primeFactorsList h)

中文:
定理 le_of_mem_primeFactorsList
  条件: {n p : 自然数} (h : p in n.primeFactorsList)
  结论: p <= n
  证明: by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · rw [primeFactorsList_zero] at h
    cases h
  · exact le_of_dvd hn (dvd_of_mem_primeFactorsList h)

Depends on / 依赖: dvd_of_mem_primeFactorsList, eq_zero_or_pos, le_of_dvd, n.eq_zero_or_pos, primeFactorsList_zero
-/
theorem le_of_mem_primeFactorsList {n p : Nat} (h : p in n.primeFactorsList) : p <= n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · rw [primeFactorsList_zero] at h
    cases h
  · exact le_of_dvd hn (dvd_of_mem_primeFactorsList h)

/--
theorem `primeFactorsList_unique` / 定理 `primeFactorsList_unique`

English:
theorem primeFactorsList_unique
  given: {n : Nat} {l : List Nat} (h₁ : prod l = n) (h₂ : forall p in l, Prime p)
  proof: by
  refine perm_of_prod_eq_prod ?_ ?_ ?_
  · rw [h₁]
    refine (prod_primeFactorsList ?_).symm
    rintro rfl
    rw [prod_eq_zero_iff] at h₁
    exact Prime.ne_zero (h₂ 0 h₁) rfl
  · simp_rw [← prime_iff]
    exact h₂
  · simp_rw [← prime_iff]
    exact fun p => prime_of_mem_primeFactorsList

中文:
定理 primeFactorsList_unique
  条件: {n : 自然数} {l : 列表 自然数} (h₁ : 乘积 l = n) (h₂ : 对任意 p in l, 素 p)
  证明: by
  refine perm_of_prod_eq_prod ?_ ?_ ?_
  · rw [h₁]
    refine (prod_primeFactorsList ?_).symm
    rintro rfl
    rw [prod_eq_zero_iff] at h₁
    exact Prime.ne_zero (h₂ 0 h₁) rfl
  · simp_rw [← prime_iff]
    exact h₂
  · simp_rw [← prime_iff]
    exact fun p => prime_of_mem_primeFactorsList

Depends on / 依赖: Prime.ne_zero, ne_zero, perm_of_prod_eq_prod, prime_iff, prime_of_mem_primeFactorsList, prod_eq_zero_iff, prod_primeFactorsList, simp_rw
-/
theorem primeFactorsList_unique {n : Nat} {l : List Nat} (h₁ : prod l = n) (h₂ : forall p in l, Prime p) :
    l ~ primeFactorsList n := by
  refine perm_of_prod_eq_prod ?_ ?_ ?_
  · rw [h₁]
    refine (prod_primeFactorsList ?_).symm
    rintro rfl
    rw [prod_eq_zero_iff] at h₁
    exact Prime.ne_zero (h₂ 0 h₁) rfl
  · simp_rw [← prime_iff]
    exact h₂
  · simp_rw [← prime_iff]
    exact fun p => prime_of_mem_primeFactorsList

/--
theorem `Prime.primeFactorsList_pow` / 定理 `Prime.primeFactorsList_pow`

English:
theorem Prime.primeFactorsList_pow
  given: {p : Nat} (hp : p.Prime) (n : Nat)
  proof: by
  symm
  rw [← List.replicate_perm]
  apply Nat.primeFactorsList_unique (List.prod_replicate n p)
  intro q hq
  rwa [eq_of_mem_replicate hq]

中文:
定理 素.primeFactorsList_pow
  条件: {p : 自然数} (hp : p.素) (n : 自然数)
  证明: by
  symm
  rw [← List.replicate_perm]
  apply Nat.primeFactorsList_unique (List.prod_replicate n p)
  intro q hq
  rwa [eq_of_mem_replicate hq]

Depends on / 依赖: List.prod_replicate, List.replicate_perm, Nat.primeFactorsList_unique, eq_of_mem_replicate, primeFactorsList_unique, prod_replicate, replicate_perm
-/
theorem Prime.primeFactorsList_pow {p : Nat} (hp : p.Prime) (n : Nat) :
    (p ^ n).primeFactorsList = List.replicate n p := by
  symm
  rw [← List.replicate_perm]
  apply Nat.primeFactorsList_unique (List.prod_replicate n p)
  intro q hq
  rwa [eq_of_mem_replicate hq]

/--
theorem `eq_prime_pow_of_unique_prime_dvd` / 定理 `eq_prime_pow_of_unique_prime_dvd`

English:
theorem eq_prime_pow_of_unique_prime_dvd
  statement: {n p : Nat} (hpos : n != 0)
  proof: by
  set k := n.primeFactorsList.length
  rw [← prod_primeFactorsList hpos]; rw [← prod_replicate k p]; rw [eq_replicate_of_mem fun d hd =>
    h (prime_of_mem_primeFactorsList hd) (dvd_of_mem_primeFactorsList hd)]

中文:
定理 eq_prime_pow_of_unique_prime_dvd
  结论: {n p : 自然数} (hpos : n != 0)
  证明: by
  set k := n.primeFactorsList.length
  rw [← prod_primeFactorsList hpos]; rw [← prod_replicate k p]; rw [eq_replicate_of_mem fun d hd =>
    h (prime_of_mem_primeFactorsList hd) (dvd_of_mem_primeFactorsList hd)]

Depends on / 依赖: dvd_of_mem_primeFactorsList, eq_replicate_of_mem, length, n.primeFactorsList.length, primeFactorsList, prime_of_mem_primeFactorsList, prod_primeFactorsList, prod_replicate
-/
theorem eq_prime_pow_of_unique_prime_dvd {n p : Nat} (hpos : n != 0)
    (h : forall {d}, Nat.Prime d -> d ∣ n -> d = p) : n = p ^ n.primeFactorsList.length := by
  set k := n.primeFactorsList.length
  rw [← prod_primeFactorsList hpos]; rw [← prod_replicate k p]; rw [eq_replicate_of_mem fun d hd =>
    h (prime_of_mem_primeFactorsList hd) (dvd_of_mem_primeFactorsList hd)]

/--
theorem `perm_primeFactorsList_mul` / 定理 `perm_primeFactorsList_mul`

English:
theorem perm_primeFactorsList_mul
  given: {a b : Nat} (ha : a != 0) (hb : b != 0)
  proof: by
  refine (primeFactorsList_unique ?_ ?_).symm
  · rw [List.prod_append, prod_primeFactorsList ha, prod_primeFactorsList hb]
  · intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp' | hp' <;> exact prime_of_mem_primeFactorsList hp'

中文:
定理 perm_primeFactorsList_mul
  条件: {a b : 自然数} (ha : a != 0) (hb : b != 0)
  证明: by
  refine (primeFactorsList_unique ?_ ?_).symm
  · rw [List.prod_append, prod_primeFactorsList ha, prod_primeFactorsList hb]
  · intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp' | hp' <;> exact prime_of_mem_primeFactorsList hp'

Depends on / 依赖: List.mem_append, List.prod_append, mem_append, primeFactorsList_unique, prime_of_mem_primeFactorsList, prod_append, prod_primeFactorsList
-/
theorem perm_primeFactorsList_mul {a b : Nat} (ha : a != 0) (hb : b != 0) :
    (a * b).primeFactorsList ~ a.primeFactorsList ++ b.primeFactorsList := by
  refine (primeFactorsList_unique ?_ ?_).symm
  · rw [List.prod_append, prod_primeFactorsList ha, prod_primeFactorsList hb]
  · intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp' | hp' <;> exact prime_of_mem_primeFactorsList hp'

/--
theorem `perm_primeFactorsList_mul_of_coprime` / 定理 `perm_primeFactorsList_mul_of_coprime`

English:
theorem perm_primeFactorsList_mul_of_coprime
  given: {a b : Nat} (hab : Coprime a b)
  proof: by
  rcases a.eq_zero_or_pos with (rfl | ha)
  · simp [(coprime_zero_left _).mp hab]
  rcases b.eq_zero_or_pos with (rfl | hb)
  · simp [(coprime_zero_right _).mp hab]
  exact perm_primeFactorsList_mul ha.ne' hb.ne'

中文:
定理 perm_primeFactorsList_mul_of_coprime
  条件: {a b : 自然数} (hab : Coprime a b)
  证明: by
  rcases a.eq_zero_or_pos with (rfl | ha)
  · simp [(coprime_zero_left _).mp hab]
  rcases b.eq_zero_or_pos with (rfl | hb)
  · simp [(coprime_zero_right _).mp hab]
  exact perm_primeFactorsList_mul ha.ne' hb.ne'

Depends on / 依赖: a.eq_zero_or_pos, b.eq_zero_or_pos, coprime_zero_left, coprime_zero_right, eq_zero_or_pos, ha.ne, hb.ne, perm_primeFactorsList_mul
-/
theorem perm_primeFactorsList_mul_of_coprime {a b : Nat} (hab : Coprime a b) :
    (a * b).primeFactorsList ~ a.primeFactorsList ++ b.primeFactorsList := by
  rcases a.eq_zero_or_pos with (rfl | ha)
  · simp [(coprime_zero_left _).mp hab]
  rcases b.eq_zero_or_pos with (rfl | hb)
  · simp [(coprime_zero_right _).mp hab]
  exact perm_primeFactorsList_mul ha.ne' hb.ne'

/--
theorem `primeFactorsList_sublist_right` / 定理 `primeFactorsList_sublist_right`

English:
theorem primeFactorsList_sublist_right
  given: {n k : Nat} (h : k != 0)
  proof: by
  rcases n with - | hn
  · simp [zero_mul]
  apply sublist_of_subperm_of_pairwise _
    (primeFactorsList_sorted _).pairwise (primeFactorsList_sorted _).pairwise
  simp only [(perm_primeFactorsList_mul (Nat.succ_ne_zero _) h).subperm_left]
  exact (sublist_append_left _ _).subperm

中文:
定理 primeFactorsList_sublist_right
  条件: {n k : 自然数} (h : k != 0)
  证明: by
  rcases n with - | hn
  · simp [zero_mul]
  apply sublist_of_subperm_of_pairwise _
    (primeFactorsList_sorted _).pairwise (primeFactorsList_sorted _).pairwise
  simp only [(perm_primeFactorsList_mul (Nat.succ_ne_zero _) h).subperm_left]
  exact (sublist_append_left _ _).subperm

Depends on / 依赖: Nat.succ_ne_zero, pairwise, perm_primeFactorsList_mul, primeFactorsList_sorted, sublist_append_left, sublist_of_subperm_of_pairwise, subperm, subperm_left, succ_ne_zero, zero_mul
-/
theorem primeFactorsList_sublist_right {n k : Nat} (h : k != 0) :
    n.primeFactorsList <+ (n * k).primeFactorsList := by
  rcases n with - | hn
  · simp [zero_mul]
  apply sublist_of_subperm_of_pairwise _
    (primeFactorsList_sorted _).pairwise (primeFactorsList_sorted _).pairwise
  simp only [(perm_primeFactorsList_mul (Nat.succ_ne_zero _) h).subperm_left]
  exact (sublist_append_left _ _).subperm

/--
theorem `primeFactorsList_sublist_of_dvd` / 定理 `primeFactorsList_sublist_of_dvd`

English:
theorem primeFactorsList_sublist_of_dvd
  given: {n k : Nat} (h : n ∣ k) (h' : k != 0)
  proof: by
  obtain ⟨a, rfl⟩ := h
  exact primeFactorsList_sublist_right (right_ne_zero_of_mul h')

中文:
定理 primeFactorsList_sublist_of_dvd
  条件: {n k : 自然数} (h : n ∣ k) (h' : k != 0)
  证明: by
  obtain ⟨a, rfl⟩ := h
  exact primeFactorsList_sublist_right (right_ne_zero_of_mul h')

Depends on / 依赖: primeFactorsList_sublist_right, right_ne_zero_of_mul
-/
theorem primeFactorsList_sublist_of_dvd {n k : Nat} (h : n ∣ k) (h' : k != 0) :
    n.primeFactorsList <+ k.primeFactorsList := by
  obtain ⟨a, rfl⟩ := h
  exact primeFactorsList_sublist_right (right_ne_zero_of_mul h')

/--
theorem `primeFactorsList_subset_right` / 定理 `primeFactorsList_subset_right`

English:
theorem primeFactorsList_subset_right
  given: {n k : Nat} (h : k != 0)
  proof: (primeFactorsList_sublist_right h).subset

中文:
定理 primeFactorsList_subset_right
  条件: {n k : 自然数} (h : k != 0)
  证明: (primeFactorsList_sublist_right h).subset

Depends on / 依赖: primeFactorsList_sublist_right, subset
-/
theorem primeFactorsList_subset_right {n k : Nat} (h : k != 0) :
    n.primeFactorsList subseteq (n * k).primeFactorsList :=
  (primeFactorsList_sublist_right h).subset

/--
theorem `primeFactorsList_subset_of_dvd` / 定理 `primeFactorsList_subset_of_dvd`

English:
theorem primeFactorsList_subset_of_dvd
  given: {n k : Nat} (h : n ∣ k) (h' : k != 0)
  proof: (primeFactorsList_sublist_of_dvd h h').subset

中文:
定理 primeFactorsList_subset_of_dvd
  条件: {n k : 自然数} (h : n ∣ k) (h' : k != 0)
  证明: (primeFactorsList_sublist_of_dvd h h').subset

Depends on / 依赖: primeFactorsList_sublist_of_dvd, subset
-/
theorem primeFactorsList_subset_of_dvd {n k : Nat} (h : n ∣ k) (h' : k != 0) :
    n.primeFactorsList subseteq k.primeFactorsList :=
  (primeFactorsList_sublist_of_dvd h h').subset

/--
theorem `dvd_of_primeFactorsList_subperm` / 定理 `dvd_of_primeFactorsList_subperm`

English:
theorem dvd_of_primeFactorsList_subperm
  statement: {a b : Nat} (ha : a != 0)
  proof: by
  rcases b.eq_zero_or_pos with (rfl | hb)
  · exact dvd_zero _
  rcases a with (_ | _ | a)
  · exact (ha rfl).elim
  · exact one_dvd _
  use (b.primeFactorsList.diff a.succ.succ.primeFactorsList).prod
  nth_rw 1 [← Nat.prod_primeFactorsList ha]
  rw [← List.prod_append]; rw [List.Perm.prod_eq Lis

中文:
定理 dvd_of_primeFactorsList_subperm
  结论: {a b : 自然数} (ha : a != 0)
  证明: by
  rcases b.eq_zero_or_pos with (rfl | hb)
  · exact dvd_zero _
  rcases a with (_ | _ | a)
  · exact (ha rfl).elim
  · exact one_dvd _
  use (b.primeFactorsList.diff a.succ.succ.primeFactorsList).prod
  nth_rw 1 [← Nat.prod_primeFactorsList ha]
  rw [← List.prod_append]; rw [List.Perm.prod_eq Lis

Depends on / 依赖: List.Perm.prod_eq, List.prod_append, List.subperm_append_diff_self_of_count_le, List.subperm_ext_iff.mp, Nat.prod_primeFactorsList, a.succ.succ.primeFactorsList, b.eq_zero_or_pos, b.primeFactorsList.diff, dvd_zero, eq_zero_or_pos, hb.ne, nth_rw, one_dvd, primeFactorsList, prod_append, prod_eq, prod_primeFactorsList, subperm_append_diff_self_of_count_le, subperm_ext_iff
-/
theorem dvd_of_primeFactorsList_subperm {a b : Nat} (ha : a != 0)
    (h : a.primeFactorsList <+~ b.primeFactorsList) : a ∣ b := by
  rcases b.eq_zero_or_pos with (rfl | hb)
  · exact dvd_zero _
  rcases a with (_ | _ | a)
  · exact (ha rfl).elim
  · exact one_dvd _
  use (b.primeFactorsList.diff a.succ.succ.primeFactorsList).prod
  nth_rw 1 [← Nat.prod_primeFactorsList ha]
  rw [← List.prod_append]; rw [List.Perm.prod_eq List.subperm_append_diff_self_of_count_le List.subperm_ext_iff.mp h]; rw [Nat.prod_primeFactorsList hb.ne']

/--
theorem `replicate_subperm_primeFactorsList_iff` / 定理 `replicate_subperm_primeFactorsList_iff`

English:
theorem replicate_subperm_primeFactorsList_iff
  given: {a b n : Nat} (ha : Prime a) (hb : b != 0)
  proof: by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    constructor
    · rw [List.subperm_iff]
      rintro ⟨u, hu1, hu2⟩
      rw [← Nat.prod_primeFactorsList hb]; rw [← hu1.prod_eq]; rw [← prod_replicate]
      exact hu2.prod_dvd_prod
    · rintro ⟨c, rfl⟩
      rw [Ne]; rw [po

中文:
定理 replicate_subperm_primeFactorsList_iff
  条件: {a b n : 自然数} (ha : 素 a) (hb : b != 0)
  证明: by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    constructor
    · rw [List.subperm_iff]
      rintro ⟨u, hu1, hu2⟩
      rw [← Nat.prod_primeFactorsList hb]; rw [← hu1.prod_eq]; rw [← prod_replicate]
      exact hu2.prod_dvd_prod
    · rintro ⟨c, rfl⟩
      rw [Ne]; rw [po

Depends on / 依赖: List.subperm_iff, Nat.perm_primeFactorsList_mul, Nat.prod_primeFactorsList, _root_, _root_.not_or, generalizing, hu1.prod_eq, hu2.prod_dvd_prod, mul_assoc, mul_eq_zero, not_or, perm_primeFactorsList_mul, pow_succ, primeFactorsList_prime, prod_dvd_prod, prod_eq, prod_primeFactorsList, prod_replicate, replicate_succ, singleton_append
-/
theorem replicate_subperm_primeFactorsList_iff {a b n : Nat} (ha : Prime a) (hb : b != 0) :
    replicate n a <+~ primeFactorsList b ↔ a ^ n ∣ b := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    constructor
    · rw [List.subperm_iff]
      rintro ⟨u, hu1, hu2⟩
      rw [← Nat.prod_primeFactorsList hb]; rw [← hu1.prod_eq]; rw [← prod_replicate]
      exact hu2.prod_dvd_prod
    · rintro ⟨c, rfl⟩
      rw [Ne]; rw [pow_succ']; rw [mul_assoc]; rw [mul_eq_zero]; rw [_root_.not_or] at hb
      rw [pow_succ']; rw [mul_assoc]; rw [replicate_succ]; rw [(Nat.perm_primeFactorsList_mul hb.1 hb.2).subperm_left]; rw [primeFactorsList_prime ha]; rw [singleton_append]; rw [subperm_cons]; rw [ih hb.2]
      exact dvd_mul_right _ _

end

/--
theorem `mem_primeFactorsList_mul` / 定理 `mem_primeFactorsList_mul`

English:
theorem mem_primeFactorsList_mul
  given: {a b : Nat} (ha : a != 0) (hb : b != 0) {p : Nat}
  proof: by
  rw [mem_primeFactorsList (mul_ne_zero ha hb)]; rw [mem_primeFactorsList ha]; rw [mem_primeFactorsList hb]; rw [← and_or_left]
  simpa only [and_congr_right_iff] using Prime.dvd_mul

中文:
定理 mem_primeFactorsList_mul
  条件: {a b : 自然数} (ha : a != 0) (hb : b != 0) {p : 自然数}
  证明: by
  rw [mem_primeFactorsList (mul_ne_zero ha hb)]; rw [mem_primeFactorsList ha]; rw [mem_primeFactorsList hb]; rw [← and_or_left]
  simpa only [and_congr_right_iff] using Prime.dvd_mul

Depends on / 依赖: Prime.dvd_mul, and_congr_right_iff, and_or_left, dvd_mul, mem_primeFactorsList, mul_ne_zero
-/
theorem mem_primeFactorsList_mul {a b : Nat} (ha : a != 0) (hb : b != 0) {p : Nat} :
    p in (a * b).primeFactorsList ↔ p in a.primeFactorsList ∨ p in b.primeFactorsList := by
  rw [mem_primeFactorsList (mul_ne_zero ha hb)]; rw [mem_primeFactorsList ha]; rw [mem_primeFactorsList hb]; rw [← and_or_left]
  simpa only [and_congr_right_iff] using Prime.dvd_mul

/--
theorem `coprime_primeFactorsList_disjoint` / 定理 `coprime_primeFactorsList_disjoint`

English:
theorem coprime_primeFactorsList_disjoint
  given: {a b : Nat} (hab : a.Coprime b)
  proof: by
  intro q hqa hqb
  apply not_prime_one
  rw [← eq_one_of_dvd_coprimes hab (dvd_of_mem_primeFactorsList hqa)
    (dvd_of_mem_primeFactorsList hqb)]
  exact prime_of_mem_primeFactorsList hqa

中文:
定理 coprime_primeFactorsList_disjoint
  条件: {a b : 自然数} (hab : a.Coprime b)
  证明: by
  intro q hqa hqb
  apply not_prime_one
  rw [← eq_one_of_dvd_coprimes hab (dvd_of_mem_primeFactorsList hqa)
    (dvd_of_mem_primeFactorsList hqb)]
  exact prime_of_mem_primeFactorsList hqa

Depends on / 依赖: dvd_of_mem_primeFactorsList, eq_one_of_dvd_coprimes, not_prime_one, prime_of_mem_primeFactorsList
-/
theorem coprime_primeFactorsList_disjoint {a b : Nat} (hab : a.Coprime b) :
    List.Disjoint a.primeFactorsList b.primeFactorsList := by
  intro q hqa hqb
  apply not_prime_one
  rw [← eq_one_of_dvd_coprimes hab (dvd_of_mem_primeFactorsList hqa)
    (dvd_of_mem_primeFactorsList hqb)]
  exact prime_of_mem_primeFactorsList hqa

/--
theorem `mem_primeFactorsList_mul_of_coprime` / 定理 `mem_primeFactorsList_mul_of_coprime`

English:
theorem mem_primeFactorsList_mul_of_coprime
  given: {a b : Nat} (hab : Coprime a b) (p : Nat)
  proof: by
  rcases a.eq_zero_or_pos with (rfl | ha)
  · simp [(coprime_zero_left _).mp hab]
  rcases b.eq_zero_or_pos with (rfl | hb)
  · simp [(coprime_zero_right _).mp hab]
  rw [mem_primeFactorsList_mul ha.ne' hb.ne']; rw [List.mem_union_iff]

中文:
定理 mem_primeFactorsList_mul_of_coprime
  条件: {a b : 自然数} (hab : Coprime a b) (p : 自然数)
  证明: by
  rcases a.eq_zero_or_pos with (rfl | ha)
  · simp [(coprime_zero_left _).mp hab]
  rcases b.eq_zero_or_pos with (rfl | hb)
  · simp [(coprime_zero_right _).mp hab]
  rw [mem_primeFactorsList_mul ha.ne' hb.ne']; rw [List.mem_union_iff]

Depends on / 依赖: List.mem_union_iff, a.eq_zero_or_pos, b.eq_zero_or_pos, coprime_zero_left, coprime_zero_right, eq_zero_or_pos, ha.ne, hb.ne, mem_primeFactorsList_mul, mem_union_iff
-/
theorem mem_primeFactorsList_mul_of_coprime {a b : Nat} (hab : Coprime a b) (p : Nat) :
    p in (a * b).primeFactorsList ↔ p in a.primeFactorsList union b.primeFactorsList := by
  rcases a.eq_zero_or_pos with (rfl | ha)
  · simp [(coprime_zero_left _).mp hab]
  rcases b.eq_zero_or_pos with (rfl | hb)
  · simp [(coprime_zero_right _).mp hab]
  rw [mem_primeFactorsList_mul ha.ne' hb.ne']; rw [List.mem_union_iff]

open List

/--
theorem `mem_primeFactorsList_mul_left` / 定理 `mem_primeFactorsList_mul_left`

English:
theorem mem_primeFactorsList_mul_left
  given: {p a b : Nat} (hpa : p in a.primeFactorsList) (hb : b != 0)
  proof: by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp at hpa
  apply (mem_primeFactorsList_mul ha hb).2 (Or.inl hpa)

中文:
定理 mem_primeFactorsList_mul_left
  条件: {p a b : 自然数} (hpa : p in a.primeFactorsList) (hb : b != 0)
  证明: by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp at hpa
  apply (mem_primeFactorsList_mul ha hb).2 (Or.inl hpa)

Depends on / 依赖: Or.inl, eq_or_ne, mem_primeFactorsList_mul
-/
theorem mem_primeFactorsList_mul_left {p a b : Nat} (hpa : p in a.primeFactorsList) (hb : b != 0) :
    p in (a * b).primeFactorsList := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp at hpa
  apply (mem_primeFactorsList_mul ha hb).2 (Or.inl hpa)

/--
theorem `mem_primeFactorsList_mul_right` / 定理 `mem_primeFactorsList_mul_right`

English:
theorem mem_primeFactorsList_mul_right
  given: {p a b : Nat} (hpb : p in b.primeFactorsList) (ha : a != 0)
  proof: by
  rw [mul_comm]
  exact mem_primeFactorsList_mul_left hpb ha

中文:
定理 mem_primeFactorsList_mul_right
  条件: {p a b : 自然数} (hpb : p in b.primeFactorsList) (ha : a != 0)
  证明: by
  rw [mul_comm]
  exact mem_primeFactorsList_mul_left hpb ha

Depends on / 依赖: mem_primeFactorsList_mul_left, mul_comm
-/
theorem mem_primeFactorsList_mul_right {p a b : Nat} (hpb : p in b.primeFactorsList) (ha : a != 0) :
    p in (a * b).primeFactorsList := by
  rw [mul_comm]
  exact mem_primeFactorsList_mul_left hpb ha

/--
theorem `eq_two_pow_or_exists_odd_prime_and_dvd` / 定理 `eq_two_pow_or_exists_odd_prime_and_dvd`

English:
theorem eq_two_pow_or_exists_odd_prime_and_dvd
  given: (n : Nat)
  proof: (eq_or_ne n 0).elim (fun hn => Or.inr ⟨3, prime_three, hn.symm ▸ dvd_zero 3, ⟨1, rfl⟩⟩) fun hn =>
    or_iff_not_imp_right.mpr fun H =>
      ⟨n.primeFactorsList.length,
        eq_prime_pow_of_unique_prime_dvd hn fun {_} hprime hdvd =>
          hprime.eq_two_or_odd'.resolve_right fun hodd => H ⟨_,

中文:
定理 eq_two_pow_or_存在_odd_prime_and_dvd
  条件: (n : 自然数)
  证明: (eq_or_ne n 0).elim (fun hn => Or.inr ⟨3, prime_three, hn.symm ▸ dvd_zero 3, ⟨1, rfl⟩⟩) fun hn =>
    or_iff_not_imp_right.mpr fun H =>
      ⟨n.primeFactorsList.length,
        eq_prime_pow_of_unique_prime_dvd hn fun {_} hprime hdvd =>
          hprime.eq_two_or_odd'.resolve_right fun hodd => H ⟨_,

Depends on / 依赖: Or.inr, dvd_zero, eq_or_ne, eq_prime_pow_of_unique_prime_dvd, eq_two_or_odd, hn.symm, hprime, hprime.eq_two_or_odd, length, n.primeFactorsList.length, or_iff_not_imp_right, or_iff_not_imp_right.mpr, primeFactorsList, prime_three, resolve_right
-/
theorem eq_two_pow_or_exists_odd_prime_and_dvd (n : Nat) :
    (exists k : Nat, n = 2 ^ k) ∨ exists p, Nat.Prime p ∧ p ∣ n ∧ Odd p :=
  (eq_or_ne n 0).elim (fun hn => Or.inr ⟨3, prime_three, hn.symm ▸ dvd_zero 3, ⟨1, rfl⟩⟩) fun hn =>
    or_iff_not_imp_right.mpr fun H =>
      ⟨n.primeFactorsList.length,
        eq_prime_pow_of_unique_prime_dvd hn fun {_} hprime hdvd =>
          hprime.eq_two_or_odd'.resolve_right fun hodd => H ⟨_, hprime, hdvd, hodd⟩⟩

/--
theorem `four_dvd_or_exists_odd_prime_and_dvd_of_two_lt` / 定理 `four_dvd_or_exists_odd_prime_and_dvd_of_two_lt`

English:
theorem four_dvd_or_exists_odd_prime_and_dvd_of_two_lt
  given: {n : Nat} (n2 : 2 < n)
  proof: by
  obtain ⟨_ | _ | k, rfl⟩ | ⟨p, hp, hdvd, hodd⟩ := n.eq_two_pow_or_exists_odd_prime_and_dvd
  · contradiction
  · contradiction
  · simp [Nat.pow_succ, mul_assoc]
  · exact Or.inr ⟨p, hp, hdvd, hodd⟩

中文:
定理 four_dvd_or_存在_odd_prime_and_dvd_of_two_lt
  条件: {n : 自然数} (n2 : 2 < n)
  证明: by
  obtain ⟨_ | _ | k, rfl⟩ | ⟨p, hp, hdvd, hodd⟩ := n.eq_two_pow_or_exists_odd_prime_and_dvd
  · contradiction
  · contradiction
  · simp [Nat.pow_succ, mul_assoc]
  · exact Or.inr ⟨p, hp, hdvd, hodd⟩

Depends on / 依赖: Nat.pow_succ, Or.inr, eq_two_pow_or_exists_odd_prime_and_dvd, mul_assoc, n.eq_two_pow_or_exists_odd_prime_and_dvd, pow_succ
-/
theorem four_dvd_or_exists_odd_prime_and_dvd_of_two_lt {n : Nat} (n2 : 2 < n) :
    4 ∣ n ∨ exists p, Prime p ∧ p ∣ n ∧ Odd p := by
  obtain ⟨_ | _ | k, rfl⟩ | ⟨p, hp, hdvd, hodd⟩ := n.eq_two_pow_or_exists_odd_prime_and_dvd
  · contradiction
  · contradiction
  · simp [Nat.pow_succ, mul_assoc]
  · exact Or.inr ⟨p, hp, hdvd, hodd⟩

end Nat
