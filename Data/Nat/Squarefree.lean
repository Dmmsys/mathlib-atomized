/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.Divisors
public import Mathlib.RingTheory.UniqueFactorizationDomain.Nat

/-!
# Lemmas about squarefreeness of natural numbers

A number is squarefree when it is not divisible by any squares except the squares of units.

## Main Results
- `Nat.squarefree_iff_nodup_primeFactorsList`: A positive natural number `x` is squarefree iff
  the list `factors x` has no duplicate factors.

## Tags
squarefree, multiplicity

-/

@[expose] public section

open Finset

namespace Nat

/--
theorem `squarefree_iff_nodup_primeFactorsList` / 定理 `squarefree_iff_nodup_primeFactorsList`

English:
theorem squarefree_iff_nodup_primeFactorsList
  given: {n : Nat} (h0 : n != 0)
  proof: by
  rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0]; rw [Nat.factors_eq]
  simp

中文:
定理 squarefree_iff_nodup_primeFactorsList
  条件: {n : 自然数} (h0 : n != 0)
  证明: by
  rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0]; rw [Nat.factors_eq]
  simp

Depends on / 依赖: B.val, Function, Function.comp_apply, IsScalarTower, IsScalarTower.algebraMap_apply, Nat.factors_eq, UniqueFactorizationMonoid, UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors, algebraMap_apply, coe_val, comp_apply, deriv_algebraMap, factors_eq, inst.isLiouville, isLiouville, logDeriv_algebraMap, simp_rw, squarefree_iff_nodup_normalizedFactors
-/
theorem squarefree_iff_nodup_primeFactorsList {n : Nat} (h0 : n != 0) :
    Squarefree n ↔ n.primeFactorsList.Nodup := by
  rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0]; rw [Nat.factors_eq]
  simp

end Nat

/--
theorem `Squarefree.nodup_primeFactorsList` / 定理 `Squarefree.nodup_primeFactorsList`

English:
theorem Squarefree.nodup_primeFactorsList
  given: {n : Nat} (hn : Squarefree n)
  statement: n.primeFactorsList.Nodup
  proof: (Nat.squarefree_iff_nodup_primeFactorsList hn.ne_zero).mp hn

中文:
定理 Squarefree.nodup_primeFactorsList
  条件: {n : 自然数} (hn : Squarefree n)
  结论: n.primeFactorsList.Nodup
  证明: (Nat.squarefree_iff_nodup_primeFactorsList hn.ne_zero).mp hn

Depends on / 依赖: Nat.squarefree_iff_nodup_primeFactorsList, hn.ne_zero, ne_zero, squarefree_iff_nodup_primeFactorsList
-/
theorem Squarefree.nodup_primeFactorsList {n : Nat} (hn : Squarefree n) : n.primeFactorsList.Nodup :=
  (Nat.squarefree_iff_nodup_primeFactorsList hn.ne_zero).mp hn

namespace Nat
variable {s : Finset Nat} {m n p : Nat}

/--
theorem `squarefree_iff_prime_squarefree` / 定理 `squarefree_iff_prime_squarefree`

English:
theorem squarefree_iff_prime_squarefree
  given: {n : Nat}
  statement: Squarefree n ↔ forall x, Prime x -> ¬x * x ∣ n
  proof: squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible ⟨_, prime_two⟩

中文:
定理 squarefree_iff_prime_squarefree
  条件: {n : 自然数}
  结论: Squarefree n ↔ 对任意 x, Prime x -> ¬x * x ∣ n
  证明: squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible ⟨_, prime_two⟩

Depends on / 依赖: prime_two, squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible
-/
theorem squarefree_iff_prime_squarefree {n : Nat} : Squarefree n ↔ forall x, Prime x -> ¬x * x ∣ n :=
  squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible ⟨_, prime_two⟩

/--
theorem `_root_.Squarefree.natFactorization_le_one` / 定理 `_root_.Squarefree.natFactorization_le_one`

English:
theorem _root_.Squarefree.natFactorization_le_one
  given: {n : Nat} (p : Nat) (hn : Squarefree n)
  proof: by
  rcases eq_or_ne n 0 with (rfl | hn')
  · simp
  rw [squarefree_iff_emultiplicity_le_one] at hn
  by_cases hp : p.Prime
  · have := hn p
    rw [← multiplicity_eq_factorization hp hn']
    simp only [Nat.isUnit_iff, hp.ne_one, or_false] at this
    exact multiplicity_le_of_emultiplicity_le this


中文:
定理 _root_.Squarefree.natFactorization_le_one
  条件: {n : 自然数} (p : 自然数) (hn : Squarefree n)
  证明: by
  rcases eq_or_ne n 0 with (rfl | hn')
  · simp
  rw [squarefree_iff_emultiplicity_le_one] at hn
  by_cases hp : p.Prime
  · have := hn p
    rw [← multiplicity_eq_factorization hp hn']
    simp only [Nat.isUnit_iff, hp.ne_one, or_false] at this
    exact multiplicity_le_of_emultiplicity_le this


Depends on / 依赖: Nat.isUnit_iff, eq_or_ne, factorization_eq_zero_of_not_prime, hp.ne_one, isUnit_iff, multiplicity_eq_factorization, multiplicity_le_of_emultiplicity_le, ne_one, or_false, p.Prime, squarefree_iff_emultiplicity_le_one, zero_le_one
-/
theorem _root_.Squarefree.natFactorization_le_one {n : Nat} (p : Nat) (hn : Squarefree n) :
    n.factorization p <= 1 := by
  rcases eq_or_ne n 0 with (rfl | hn')
  · simp
  rw [squarefree_iff_emultiplicity_le_one] at hn
  by_cases hp : p.Prime
  · have := hn p
    rw [← multiplicity_eq_factorization hp hn']
    simp only [Nat.isUnit_iff, hp.ne_one, or_false] at this
    exact multiplicity_le_of_emultiplicity_le this
  · rw [factorization_eq_zero_of_not_prime _ hp]
    exact zero_le_one

/--
lemma `factorization_eq_one_of_squarefree` / 引理 `factorization_eq_one_of_squarefree`

English:
lemma factorization_eq_one_of_squarefree
  given: (hn : Squarefree n) (hp : p.Prime) (hpn : p ∣ n)
  proof: (hn.natFactorization_le_one _).antisymm (hp.dvd_iff_one_le_factorization hn.ne_zero).1 hpn

中文:
引理 factorization_eq_one_of_squarefree
  条件: (hn : Squarefree n) (hp : p.Prime) (hpn : p ∣ n)
  证明: (hn.natFactorization_le_one _).antisymm (hp.dvd_iff_one_le_factorization hn.ne_zero).1 hpn

Depends on / 依赖: antisymm, dvd_iff_one_le_factorization, hn.natFactorization_le_one, hn.ne_zero, hp.dvd_iff_one_le_factorization, natFactorization_le_one, ne_zero
-/
lemma factorization_eq_one_of_squarefree (hn : Squarefree n) (hp : p.Prime) (hpn : p ∣ n) :
    factorization n p = 1 :=
(hn.natFactorization_le_one _).antisymm (hp.dvd_iff_one_le_factorization hn.ne_zero).1 hpn

/--
theorem `squarefree_of_factorization_le_one` / 定理 `squarefree_of_factorization_le_one`

English:
theorem squarefree_of_factorization_le_one
  given: {n : Nat} (hn : n != 0) (hn' : forall p, n.factorization p <= 1)
  proof: by
  rw [squarefree_iff_nodup_primeFactorsList hn]; rw [List.nodup_iff_count_le_one]
  intro a
  rw [primeFactorsList_count_eq]
  apply hn'

中文:
定理 squarefree_of_factorization_le_one
  条件: {n : 自然数} (hn : n != 0) (hn' : 对任意 p, n.factorization p <= 1)
  证明: by
  rw [squarefree_iff_nodup_primeFactorsList hn]; rw [List.nodup_iff_count_le_one]
  intro a
  rw [primeFactorsList_count_eq]
  apply hn'

Depends on / 依赖: List.nodup_iff_count_le_one, nodup_iff_count_le_one, primeFactorsList_count_eq, squarefree_iff_nodup_primeFactorsList
-/
theorem squarefree_of_factorization_le_one {n : Nat} (hn : n != 0) (hn' : forall p, n.factorization p <= 1) :
    Squarefree n := by
  rw [squarefree_iff_nodup_primeFactorsList hn]; rw [List.nodup_iff_count_le_one]
  intro a
  rw [primeFactorsList_count_eq]
  apply hn'

/--
theorem `squarefree_iff_factorization_le_one` / 定理 `squarefree_iff_factorization_le_one`

English:
theorem squarefree_iff_factorization_le_one
  given: {n : Nat} (hn : n != 0)
  proof: ⟨fun hn => hn.natFactorization_le_one, squarefree_of_factorization_le_one hn⟩

中文:
定理 squarefree_iff_factorization_le_one
  条件: {n : 自然数} (hn : n != 0)
  证明: ⟨fun hn => hn.natFactorization_le_one, squarefree_of_factorization_le_one hn⟩

Depends on / 依赖: hn.natFactorization_le_one, natFactorization_le_one, squarefree_of_factorization_le_one
-/
theorem squarefree_iff_factorization_le_one {n : Nat} (hn : n != 0) :
    Squarefree n ↔ forall p, n.factorization p <= 1 :=
  ⟨fun hn => hn.natFactorization_le_one, squarefree_of_factorization_le_one hn⟩

/--
theorem `Squarefree.ext_iff` / 定理 `Squarefree.ext_iff`

English:
theorem Squarefree.ext_iff
  given: {n m : Nat} (hn : Squarefree n) (hm : Squarefree m)
  proof: by
  refine ⟨by rintro rfl; simp, fun h => eq_of_factorization_eq hn.ne_zero hm.ne_zero fun p => ?_⟩
  by_cases hp : p.Prime
  · have h₁ := h _ hp
    rw [← not_iff_not]; rw [hp.dvd_iff_one_le_factorization hn.ne_zero]; rw [not_le]; rw [lt_one_iff]; rw [hp.dvd_iff_one_le_factorization hm.ne_zero]; r

中文:
定理 Squarefree.ext_iff
  条件: {n m : 自然数} (hn : Squarefree n) (hm : Squarefree m)
  证明: by
  refine ⟨by rintro rfl; simp, fun h => eq_of_factorization_eq hn.ne_zero hm.ne_zero fun p => ?_⟩
  by_cases hp : p.Prime
  · have h₁ := h _ hp
    rw [← not_iff_not]; rw [hp.dvd_iff_one_le_factorization hn.ne_zero]; rw [not_le]; rw [lt_one_iff]; rw [hp.dvd_iff_one_le_factorization hm.ne_zero]; r

Depends on / 依赖: dvd_iff_one_le_factorization, eq_of_factorization_eq, factorization_eq_zero_of_not_prime, hm.natFactorization_le_one, hm.ne_zero, hn.natFactorization_le_one, hn.ne_zero, hp.dvd_iff_one_le_factorization, lt_one_iff, natFactorization_le_one, ne_zero, not_iff_not, not_le, p.Prime
-/
theorem Squarefree.ext_iff {n m : Nat} (hn : Squarefree n) (hm : Squarefree m) :
    n = m ↔ forall p, Prime p -> (p ∣ n ↔ p ∣ m) := by
  refine ⟨by rintro rfl; simp, fun h => eq_of_factorization_eq hn.ne_zero hm.ne_zero fun p => ?_⟩
  by_cases hp : p.Prime
  · have h₁ := h _ hp
    rw [← not_iff_not]; rw [hp.dvd_iff_one_le_factorization hn.ne_zero]; rw [not_le]; rw [lt_one_iff]; rw [hp.dvd_iff_one_le_factorization hm.ne_zero]; rw [not_le]; rw [lt_one_iff] at h₁
    have h₂ := hn.natFactorization_le_one p
    have h₃ := hm.natFactorization_le_one p
    lia
  rw [factorization_eq_zero_of_not_prime _ hp]; rw [factorization_eq_zero_of_not_prime _ hp]

/--
theorem `squarefree_pow_iff` / 定理 `squarefree_pow_iff`

English:
theorem squarefree_pow_iff
  given: {n k : Nat} (hn : n != 1) (hk : k != 0)
  proof: by
  refine ⟨fun h => ?_, by rintro ⟨hn, rfl⟩; simpa⟩
  rcases eq_or_ne n 0 with (rfl | -)
  · simp [zero_pow hk] at h
  refine ⟨h.squarefree_of_dvd (dvd_pow_self _ hk), by_contradiction fun h₁ => ?_⟩
  have : 2 <= k := k.two_le_iff.mpr ⟨hk, h₁⟩
  apply hn (Nat.isUnit_iff.1 (h _ _))
  rw [← sq]
  ex

中文:
定理 squarefree_pow_iff
  条件: {n k : 自然数} (hn : n != 1) (hk : k != 0)
  证明: by
  refine ⟨fun h => ?_, by rintro ⟨hn, rfl⟩; simpa⟩
  rcases eq_or_ne n 0 with (rfl | -)
  · simp [zero_pow hk] at h
  refine ⟨h.squarefree_of_dvd (dvd_pow_self _ hk), by_contradiction fun h₁ => ?_⟩
  have : 2 <= k := k.two_le_iff.mpr ⟨hk, h₁⟩
  apply hn (Nat.isUnit_iff.1 (h _ _))
  rw [← sq]
  ex

Depends on / 依赖: Nat.isUnit_iff, by_contradiction, dvd_pow_self, eq_or_ne, h.squarefree_of_dvd, isUnit_iff, k.two_le_iff.mpr, pow_dvd_pow, squarefree_of_dvd, two_le_iff, zero_pow
-/
theorem squarefree_pow_iff {n k : Nat} (hn : n != 1) (hk : k != 0) :
    Squarefree (n ^ k) ↔ Squarefree n ∧ k = 1 := by
  refine ⟨fun h => ?_, by rintro ⟨hn, rfl⟩; simpa⟩
  rcases eq_or_ne n 0 with (rfl | -)
  · simp [zero_pow hk] at h
  refine ⟨h.squarefree_of_dvd (dvd_pow_self _ hk), by_contradiction fun h₁ => ?_⟩
  have : 2 <= k := k.two_le_iff.mpr ⟨hk, h₁⟩
  apply hn (Nat.isUnit_iff.1 (h _ _))
  rw [← sq]
  exact pow_dvd_pow _ this

/--
theorem `squarefree_and_prime_pow_iff_prime` / 定理 `squarefree_and_prime_pow_iff_prime`

English:
theorem squarefree_and_prime_pow_iff_prime
  given: {n : Nat}
  statement: Squarefree n ∧ IsPrimePow n ↔ Prime n
  proof: by
  refine ⟨?_, fun hn => ⟨hn.squarefree, hn.isPrimePow⟩⟩
  rw [isPrimePow_nat_iff]
  rintro ⟨h, p, k, hp, hk, rfl⟩
  rw [squarefree_pow_iff hp.ne_one hk.ne'] at h
  rwa [h.2, pow_one]

中文:
定理 squarefree_and_prime_pow_iff_prime
  条件: {n : 自然数}
  结论: Squarefree n ∧ IsPrimePow n ↔ Prime n
  证明: by
  refine ⟨?_, fun hn => ⟨hn.squarefree, hn.isPrimePow⟩⟩
  rw [isPrimePow_nat_iff]
  rintro ⟨h, p, k, hp, hk, rfl⟩
  rw [squarefree_pow_iff hp.ne_one hk.ne'] at h
  rwa [h.2, pow_one]

Depends on / 依赖: hk.ne, hn.isPrimePow, hn.squarefree, hp.ne_one, isPrimePow, isPrimePow_nat_iff, ne_one, pow_one, squarefree, squarefree_pow_iff
-/
theorem squarefree_and_prime_pow_iff_prime {n : Nat} : Squarefree n ∧ IsPrimePow n ↔ Prime n := by
  refine ⟨?_, fun hn => ⟨hn.squarefree, hn.isPrimePow⟩⟩
  rw [isPrimePow_nat_iff]
  rintro ⟨h, p, k, hp, hk, rfl⟩
  rw [squarefree_pow_iff hp.ne_one hk.ne'] at h
  rwa [h.2, pow_one]

/--
Definition of `minSqFacAux` / `minSqFacAux` 的定义

English:
definition minSqFacAux
  signature: : Nat -> Nat -> Option Nat
  body: by
        exact Nat.minFac_lemma n k h
      if k ∣ n then
        let n' := n / k
        have : Nat.sqrt n' - k < Nat.sqrt n + 2 - k :=
        lt_of_le_of_lt (by gcongr; apply div_le_self) this
        if k ∣ n' then some k else minSqFacAux n' (k + 2)
      else minSqFacAux n (k + 2)
termination

中文:
定义 minSqFacAux
  签名: : 自然数 -> 自然数 -> Option 自然数
  定义体: by
        exact Nat.minFac_lemma n k h
      if k ∣ n then
        let n' := n / k
        have : Nat.sqrt n' - k < Nat.sqrt n + 2 - k :=
        lt_of_le_of_lt (by gcongr; apply div_le_self) this
        if k ∣ n' then some k else minSqFacAux n' (k + 2)
      else minSqFacAux n (k + 2)
termination

Depends on / 依赖: Nat.minFac_lemma, Nat.sqrt, div_le_self, lt_of_le_of_lt, minFac_lemma, minSqFacAux, termination_by
-/
def minSqFacAux : Nat -> Nat -> Option Nat
  | n, k =>
    if h : n < k * k then none
    else
      have : Nat.sqrt n - k < Nat.sqrt n + 2 - k := by
        exact Nat.minFac_lemma n k h
      if k ∣ n then
        let n' := n / k
        have : Nat.sqrt n' - k < Nat.sqrt n + 2 - k :=
        lt_of_le_of_lt (by gcongr; apply div_le_self) this
        if k ∣ n' then some k else minSqFacAux n' (k + 2)
      else minSqFacAux n (k + 2)
termination_by n k => sqrt n + 2 - k

/--
Definition of `minSqFac` / `minSqFac` 的定义

English:
definition minSqFac
  signature: (n : Nat)
  body: if 2 ∣ n then
    let n' := n / 2
    if 2 ∣ n' then some 2 else minSqFacAux n' 3
  else minSqFacAux n 3

中文:
定义 minSqFac
  签名: (n : 自然数)
  定义体: if 2 ∣ n then
    let n' := n / 2
    if 2 ∣ n' then some 2 else minSqFacAux n' 3
  else minSqFacAux n 3

Depends on / 依赖: minSqFacAux
-/
def minSqFac (n : Nat) : Option Nat :=
  if 2 ∣ n then
    let n' := n / 2
    if 2 ∣ n' then some 2 else minSqFacAux n' 3
  else minSqFacAux n 3

/--
Definition of `MinSqFacProp` / `MinSqFacProp` 的定义

English:
definition MinSqFacProp
  signature: (n : Nat)

中文:
定义 MinSqFacProp
  签名: (n : 自然数)
-/
def MinSqFacProp (n : Nat) : Option Nat -> Prop
  | none => Squarefree n
  | some d => Prime d ∧ d * d ∣ n ∧ forall p, Prime p -> p * p ∣ n -> d <= p

/--
theorem `minSqFacProp_div` / 定理 `minSqFacProp_div`

English:
theorem minSqFacProp_div
  statement: (n) {k} (pk : Prime k) (dk : k ∣ n) (dkk : ¬k * k ∣ n) {o}
  proof: by
  have : forall p, Prime p -> p * p ∣ n -> k * (p * p) ∣ n := fun p pp dp =>
    have :=
      (coprime_primes pk pp).2 fun e => by
        subst e
        contradiction
    (coprime_mul_iff_right.2 ⟨this, this⟩).mul_dvd_of_dvd_of_dvd dk dp
  rcases o with - | d
  · rw [MinSqFacProp, squarefree_i

中文:
定理 minSqFacProp_div
  结论: (n) {k} (pk : Prime k) (dk : k ∣ n) (dkk : ¬k * k ∣ n) {o}
  证明: by
  have : forall p, Prime p -> p * p ∣ n -> k * (p * p) ∣ n := fun p pp dp =>
    have :=
      (coprime_primes pk pp).2 fun e => by
        subst e
        contradiction
    (coprime_mul_iff_right.2 ⟨this, this⟩).mul_dvd_of_dvd_of_dvd dk dp
  rcases o with - | d
  · rw [MinSqFacProp, squarefree_i

Depends on / 依赖: MinSqFacProp, coprime_mul_iff_right, coprime_primes, dvd_div_iff_mul_dvd, dvd_mul_left, dvd_trans, mul_dvd_of_dvd_of_dvd, squarefree_iff_prime_squarefree
-/
theorem minSqFacProp_div (n) {k} (pk : Prime k) (dk : k ∣ n) (dkk : ¬k * k ∣ n) {o}
    (H : MinSqFacProp (n / k) o) : MinSqFacProp n o := by
  have : forall p, Prime p -> p * p ∣ n -> k * (p * p) ∣ n := fun p pp dp =>
    have :=
      (coprime_primes pk pp).2 fun e => by
        subst e
        contradiction
    (coprime_mul_iff_right.2 ⟨this, this⟩).mul_dvd_of_dvd_of_dvd dk dp
  rcases o with - | d
  · rw [MinSqFacProp, squarefree_iff_prime_squarefree] at H ⊢
    exact fun p pp dp => H p pp ((dvd_div_iff_mul_dvd dk).2 (this _ pp dp))
  · obtain ⟨H1, H2, H3⟩ := H
    simp only [dvd_div_iff_mul_dvd dk] at H2 H3
    exact ⟨H1, dvd_trans (dvd_mul_left _ _) H2, fun p pp dp => H3 _ pp (this _ pp dp)⟩

/--
theorem `minSqFacAux_has_prop` / 定理 `minSqFacAux_has_prop`

English:
theorem minSqFacAux_has_prop
  statement: {n : Nat} (k) (n0 : 0 < n) (i) (e : k = 2 * i + 3)
  proof: by
  rw [minSqFacAux]
  by_cases h : n < k * k <;> simp only [h, ↓reduceDIte]
  · refine squarefree_iff_prime_squarefree.2 fun p pp d => ?_
    have := ih p pp (dvd_trans ⟨_, rfl⟩ d)
    have := Nat.mul_le_mul this this
    exact not_le_of_gt h (le_trans this (le_of_dvd n0 d))
  have k2 : 2 <= k := 

中文:
定理 minSqFacAux_has_prop
  结论: {n : 自然数} (k) (n0 : 0 < n) (i) (e : k = 2 * i + 3)
  证明: by
  rw [minSqFacAux]
  by_cases h : n < k * k <;> simp only [h, ↓reduceDIte]
  · refine squarefree_iff_prime_squarefree.2 fun p pp d => ?_
    have := ih p pp (dvd_trans ⟨_, rfl⟩ d)
    have := Nat.mul_le_mul this this
    exact not_le_of_gt h (le_trans this (le_of_dvd n0 d))
  have k2 : 2 <= k := 

Depends on / 依赖: MinSqFacProp, Nat.mul_le_mul, Nat.sqrt, dvd_trans, le_of_dvd, le_trans, lt_of_lt_of_le, minSqFacAux, mul_le_mul, not_le_of_gt, reduceDIte, squarefree_iff_prime_squarefree
-/
theorem minSqFacAux_has_prop {n : Nat} (k) (n0 : 0 < n) (i) (e : k = 2 * i + 3)
    (ih : forall m, Prime m -> m ∣ n -> k <= m) : MinSqFacProp n (minSqFacAux n k) := by
  rw [minSqFacAux]
  by_cases h : n < k * k <;> simp only [h, ↓reduceDIte]
  · refine squarefree_iff_prime_squarefree.2 fun p pp d => ?_
    have := ih p pp (dvd_trans ⟨_, rfl⟩ d)
    have := Nat.mul_le_mul this this
    exact not_le_of_gt h (le_trans this (le_of_dvd n0 d))
  have k2 : 2 <= k := by lia
  have k0 : 0 < k := lt_of_lt_of_le (by decide) k2
  have IH : forall n', n' ∣ n -> ¬k ∣ n' -> MinSqFacProp n' (n'.minSqFacAux (k + 2)) := by
    intro n' nd' nk
    have hn' := le_of_dvd n0 nd'
    refine
      have : Nat.sqrt n' - k < Nat.sqrt n + 2 - k :=
        lt_of_le_of_lt (by gcongr) (Nat.minFac_lemma n k h)
      @minSqFacAux_has_prop n' (k + 2) (pos_of_dvd_of_pos nd' n0) (i + 1)
        (by simp [e, left_distrib]) fun m m2 d => ?_
    rcases Nat.eq_or_lt_of_le (ih m m2 (dvd_trans d nd')) with rfl | ml
    · contradiction
    apply (Nat.eq_or_lt_of_le ml).resolve_left
    intro me
    rw [← me]; rw [e] at d
    change 2 * (i + 2) ∣ n' at d
    have := ih _ prime_two (dvd_trans (dvd_of_mul_right_dvd d) nd')
    rw [e] at this
    exact absurd this (by lia)
  have pk : k ∣ n -> Prime k := by
    refine fun dk => prime_def_minFac.2 ⟨k2, le_antisymm (minFac_le k0) ?_⟩
    exact ih _ (minFac_prime (ne_of_gt k2)) (dvd_trans (minFac_dvd _) dk)
  split_ifs with dk dkk
  · exact ⟨pk dk, (Nat.dvd_div_iff_mul_dvd dk).1 dkk, fun p pp d => ih p pp (dvd_trans ⟨_, rfl⟩ d)⟩
  · specialize IH (n / k) (div_dvd_of_dvd dk) dkk
    exact minSqFacProp_div _ (pk dk) dk (mt (Nat.dvd_div_iff_mul_dvd dk).2 dkk) IH
  · exact IH n (dvd_refl _) dk
termination_by n.sqrt + 2 - k

/--
theorem `minSqFac_has_prop` / 定理 `minSqFac_has_prop`

English:
theorem minSqFac_has_prop
  given: (n : Nat)
  statement: MinSqFacProp n (minSqFac n)
  proof: by
  dsimp only [minSqFac]; split_ifs with d2 d4
  · exact ⟨prime_two, (dvd_div_iff_mul_dvd d2).1 d4, fun p pp _ => pp.two_le⟩
  · rcases Nat.eq_zero_or_pos n with rfl | n0
    · cases d4 (by decide)
    refine minSqFacProp_div _ prime_two d2 (mt (dvd_div_iff_mul_dvd d2).2 d4) ?_
    refine minSqFac

中文:
定理 minSqFac_has_prop
  条件: (n : 自然数)
  结论: MinSqFac命题 n (minSqFac n)
  证明: by
  dsimp only [minSqFac]; split_ifs with d2 d4
  · exact ⟨prime_two, (dvd_div_iff_mul_dvd d2).1 d4, fun p pp _ => pp.two_le⟩
  · rcases Nat.eq_zero_or_pos n with rfl | n0
    · cases d4 (by decide)
    refine minSqFacProp_div _ prime_two d2 (mt (dvd_div_iff_mul_dvd d2).2 d4) ?_
    refine minSqFac

Depends on / 依赖: Nat.div_pos, Nat.eq_zero_or_pos, div_pos, dvd_div_iff_mul_dvd, eq_zero_or_pos, le_of_dvd, lt_of_le_of_ne, minSqFac, minSqFacAux_has_prop, minSqFacProp_div, pp.two_le, prime_two, split_ifs, succ_le_of_lt, two_le
-/
theorem minSqFac_has_prop (n : Nat) : MinSqFacProp n (minSqFac n) := by
  dsimp only [minSqFac]; split_ifs with d2 d4
  · exact ⟨prime_two, (dvd_div_iff_mul_dvd d2).1 d4, fun p pp _ => pp.two_le⟩
  · rcases Nat.eq_zero_or_pos n with rfl | n0
    · cases d4 (by decide)
    refine minSqFacProp_div _ prime_two d2 (mt (dvd_div_iff_mul_dvd d2).2 d4) ?_
    refine minSqFacAux_has_prop 3 (Nat.div_pos (le_of_dvd n0 d2) (by decide)) 0 rfl ?_
    refine fun p pp dp => succ_le_of_lt (lt_of_le_of_ne pp.two_le ?_)
    rintro rfl
    contradiction
  · rcases Nat.eq_zero_or_pos n with rfl | n0
    · cases d2 (by decide)
    refine minSqFacAux_has_prop _ n0 0 rfl ?_
    refine fun p pp dp => succ_le_of_lt (lt_of_le_of_ne pp.two_le ?_)
    rintro rfl
    contradiction

/--
theorem `minSqFac_prime` / 定理 `minSqFac_prime`

English:
theorem minSqFac_prime
  given: {n d : Nat} (h : n.minSqFac = some d)
  statement: Prime d
  proof: by
  have := minSqFac_has_prop n
  rw [h] at this
  exact this.1

中文:
定理 minSqFac_prime
  条件: {n d : 自然数} (h : n.minSqFac = some d)
  结论: Prime d
  证明: by
  have := minSqFac_has_prop n
  rw [h] at this
  exact this.1

Depends on / 依赖: minSqFac_has_prop
-/
theorem minSqFac_prime {n d : Nat} (h : n.minSqFac = some d) : Prime d := by
  have := minSqFac_has_prop n
  rw [h] at this
  exact this.1

/--
theorem `minSqFac_dvd` / 定理 `minSqFac_dvd`

English:
theorem minSqFac_dvd
  given: {n d : Nat} (h : n.minSqFac = some d)
  statement: d * d ∣ n
  proof: by
  have := minSqFac_has_prop n
  rw [h] at this
  exact this.2.1

中文:
定理 minSqFac_dvd
  条件: {n d : 自然数} (h : n.minSqFac = some d)
  结论: d * d ∣ n
  证明: by
  have := minSqFac_has_prop n
  rw [h] at this
  exact this.2.1

Depends on / 依赖: minSqFac_has_prop
-/
theorem minSqFac_dvd {n d : Nat} (h : n.minSqFac = some d) : d * d ∣ n := by
  have := minSqFac_has_prop n
  rw [h] at this
  exact this.2.1

/--
theorem `minSqFac_le_of_dvd` / 定理 `minSqFac_le_of_dvd`

English:
theorem minSqFac_le_of_dvd
  given: {n d : Nat} (h : n.minSqFac = some d) {m} (m2 : 2 <= m) (md : m * m ∣ n)
  proof: by
  have := minSqFac_has_prop n; rw [h] at this
  have fd := minFac_dvd m
  exact
    le_trans (this.2.2 _ (minFac_prime <| ne_of_gt m2) (dvd_trans (mul_dvd_mul fd fd) md))
      (minFac_le <| lt_of_lt_of_le (by decide) m2)

中文:
定理 minSqFac_le_of_dvd
  条件: {n d : 自然数} (h : n.minSqFac = some d) {m} (m2 : 2 <= m) (md : m * m ∣ n)
  证明: by
  have := minSqFac_has_prop n; rw [h] at this
  have fd := minFac_dvd m
  exact
    le_trans (this.2.2 _ (minFac_prime <| ne_of_gt m2) (dvd_trans (mul_dvd_mul fd fd) md))
      (minFac_le <| lt_of_lt_of_le (by decide) m2)

Depends on / 依赖: dvd_trans, le_trans, lt_of_lt_of_le, minFac_dvd, minFac_le, minFac_prime, minSqFac_has_prop, mul_dvd_mul, ne_of_gt
-/
theorem minSqFac_le_of_dvd {n d : Nat} (h : n.minSqFac = some d) {m} (m2 : 2 <= m) (md : m * m ∣ n) :
    d <= m := by
  have := minSqFac_has_prop n; rw [h] at this
  have fd := minFac_dvd m
  exact
    le_trans (this.2.2 _ (minFac_prime <| ne_of_gt m2) (dvd_trans (mul_dvd_mul fd fd) md))
      (minFac_le <| lt_of_lt_of_le (by decide) m2)

/--
theorem `squarefree_iff_minSqFac` / 定理 `squarefree_iff_minSqFac`

English:
theorem squarefree_iff_minSqFac
  given: {n : Nat}
  statement: Squarefree n ↔ n.minSqFac = none
  proof: by
  have := minSqFac_has_prop n
  constructor <;> intro H
  · rcases e : n.minSqFac with - | d
    · rfl
    rw [e] at this
    cases squarefree_iff_prime_squarefree.1 H _ this.1 this.2.1
  · rwa [H] at this

中文:
定理 squarefree_iff_minSqFac
  条件: {n : 自然数}
  结论: Squarefree n ↔ n.minSqFac = none
  证明: by
  have := minSqFac_has_prop n
  constructor <;> intro H
  · rcases e : n.minSqFac with - | d
    · rfl
    rw [e] at this
    cases squarefree_iff_prime_squarefree.1 H _ this.1 this.2.1
  · rwa [H] at this

Depends on / 依赖: minSqFac, minSqFac_has_prop, n.minSqFac, squarefree_iff_prime_squarefree
-/
theorem squarefree_iff_minSqFac {n : Nat} : Squarefree n ↔ n.minSqFac = none := by
  have := minSqFac_has_prop n
  constructor <;> intro H
  · rcases e : n.minSqFac with - | d
    · rfl
    rw [e] at this
    cases squarefree_iff_prime_squarefree.1 H _ this.1 this.2.1
  · rwa [H] at this

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidablePred (Squarefree : Nat -> Prop)
  body: fun _ =>
  decidable_of_iff' _ squarefree_iff_minSqFac

中文:
实例 :
  签名: DecidablePred (Squarefree : 自然数 -> 命题)
  定义体: fun _ =>
  decidable_of_iff' _ squarefree_iff_minSqFac
-/
instance : DecidablePred (Squarefree : Nat -> Prop) := fun _ =>
  decidable_of_iff' _ squarefree_iff_minSqFac

/--
theorem `squarefree_two` / 定理 `squarefree_two`

English:
theorem squarefree_two
  statement: Squarefree 2
  proof: by
  rw [squarefree_iff_nodup_primeFactorsList] <;> simp

中文:
定理 squarefree_two
  结论: Squarefree 2
  证明: by
  rw [squarefree_iff_nodup_primeFactorsList] <;> simp

Depends on / 依赖: squarefree_iff_nodup_primeFactorsList
-/
theorem squarefree_two : Squarefree 2 := by
  rw [squarefree_iff_nodup_primeFactorsList] <;> simp

/--
theorem `divisors_filter_squarefree_of_squarefree` / 定理 `divisors_filter_squarefree_of_squarefree`

English:
theorem divisors_filter_squarefree_of_squarefree
  given: {n : Nat} (hn : Squarefree n)
  proof: Finset.ext fun d => ⟨@Finset.filter_subset _ _ _ _ d, fun hd =>
    Finset.mem_filter.mpr ⟨hd, hn.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd) ⟩⟩

中文:
定理 divisors_filter_squarefree_of_squarefree
  条件: {n : 自然数} (hn : Squarefree n)
  证明: Finset.ext fun d => ⟨@Finset.filter_subset _ _ _ _ d, fun hd =>
    Finset.mem_filter.mpr ⟨hd, hn.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd) ⟩⟩

Depends on / 依赖: Finset, Finset.ext, Finset.filter_subset, Finset.mem_filter.mpr, Nat.dvd_of_mem_divisors, dvd_of_mem_divisors, filter_subset, hn.squarefree_of_dvd, mem_filter, squarefree_of_dvd
-/
theorem divisors_filter_squarefree_of_squarefree {n : Nat} (hn : Squarefree n) :
    {d in n.divisors | Squarefree d} = n.divisors :=
  Finset.ext fun d => ⟨@Finset.filter_subset _ _ _ _ d, fun hd =>
    Finset.mem_filter.mpr ⟨hd, hn.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd) ⟩⟩

open UniqueFactorizationMonoid

/--
theorem `divisors_filter_squarefree` / 定理 `divisors_filter_squarefree`

English:
theorem divisors_filter_squarefree
  given: {n : Nat} (h0 : n != 0)
  proof: by
  rw [(Finset.nodup _).ext ((Finset.nodup _).map_on _)]
  · intro a
    simp only [Multiset.mem_filter, Multiset.mem_map, Finset.filter_val, ← Finset.mem_def,
      mem_divisors]
    constructor
    · rintro ⟨⟨an, h0⟩, hsq⟩
      use (UniqueFactorizationMonoid.normalizedFactors a).toFinset
      

中文:
定理 divisors_filter_squarefree
  条件: {n : 自然数} (h0 : n != 0)
  证明: by
  rw [(Finset.nodup _).ext ((Finset.nodup _).map_on _)]
  · intro a
    simp only [Multiset.mem_filter, Multiset.mem_map, Finset.filter_val, ← Finset.mem_def,
      mem_divisors]
    constructor
    · rintro ⟨⟨an, h0⟩, hsq⟩
      use (UniqueFactorizationMonoid.normalizedFactors a).toFinset
      

Depends on / 依赖: Finset, Finset.filter_val, Finset.mem_def, Finset.mem_powerset, Finset.nodup, Multiset, Multiset.mem_filter, Multiset.mem_map, Multiset.toFinset_subset, Multiset.toFinset_val, UniqueFactorizationMonoid, UniqueFactorizationMonoid.normalizedFactors, UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors, filter_val, hsq.de, map_on, mem_def, mem_divisors, mem_filter, mem_map
-/
theorem divisors_filter_squarefree {n : Nat} (h0 : n != 0) :
    {d in n.divisors | Squarefree d}.val =
      (UniqueFactorizationMonoid.normalizedFactors n).toFinset.powerset.val.map fun x =>
        x.val.prod := by
  rw [(Finset.nodup _).ext ((Finset.nodup _).map_on _)]
  · intro a
    simp only [Multiset.mem_filter, Multiset.mem_map, Finset.filter_val, ← Finset.mem_def,
      mem_divisors]
    constructor
    · rintro ⟨⟨an, h0⟩, hsq⟩
      use (UniqueFactorizationMonoid.normalizedFactors a).toFinset
      simp only [Finset.mem_powerset]
      rcases an with ⟨b, rfl⟩
      rw [mul_ne_zero_iff] at h0
      rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0.1] at hsq
      rw [Multiset.toFinset_subset]; rw [Multiset.toFinset_val]; rw [hsq.dedup]; rw [← associated_iff_eq]; rw [normalizedFactors_mul h0.1 h0.2]
      exact ⟨Multiset.subset_of_le (Multiset.le_add_right _ _), prod_normalizedFactors h0.1⟩
    · rintro ⟨s, hs, rfl⟩
      rw [Finset.mem_powerset]; rw [← Finset.val_le_iff]; rw [Multiset.toFinset_val] at hs
      have hs0 : s.val.prod != 0 := by
        rw [Ne]; rw [Multiset.prod_eq_zero_iff]
        intro con
        apply
          not_irreducible_zero
            (irreducible_of_normalized_factor 0 (Multiset.mem_dedup.1 (Multiset.mem_of_le hs con)))
      rw [(prod_normalizedFactors h0).symm.dvd_iff_dvd_right]
      refine ⟨⟨Multiset.prod_dvd_prod_of_le (le_trans hs (Multiset.dedup_le _)), h0⟩, ?_⟩
      have h :=
        UniqueFactorizationMonoid.factors_unique irreducible_of_normalized_factor
          (fun x hx =>
            irreducible_of_normalized_factor x
              (Multiset.mem_of_le (le_trans hs (Multiset.dedup_le _)) hx))
          (prod_normalizedFactors hs0)
      rw [associated_eq_eq]; rw [Multiset.rel_eq] at h
      rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hs0]; rw [h]
      apply s.nodup
  · intro x hx y hy h
    rw [← Finset.val_inj]; rw [← Multiset.rel_eq]; rw [← associated_eq_eq]
    rw [← Finset.mem_def]; rw [Finset.mem_powerset] at hx hy
    apply UniqueFactorizationMonoid.factors_unique _ _ (associated_iff_eq.2 h)
    · intro z hz
      apply irreducible_of_normalized_factor z
      · rw [← Multiset.mem_toFinset]
        apply hx hz
    · intro z hz
      apply irreducible_of_normalized_factor z
      · rw [← Multiset.mem_toFinset]
        apply hy hz

/--
theorem `sum_divisors_filter_squarefree` / 定理 `sum_divisors_filter_squarefree`

English:
theorem sum_divisors_filter_squarefree
  statement: {n : Nat} (h0 : n != 0) {α : Type*} [AddCommMonoid α]
  proof: by
  rw [Finset.sum_eq_multiset_sum]; rw [divisors_filter_squarefree h0]; rw [Multiset.map_map]; rw [Finset.sum_eq_multiset_sum]
  rfl

中文:
定理 sum_divisors_filter_squarefree
  结论: {n : 自然数} (h0 : n != 0) {α : 类型} [AddCommMonoid α]
  证明: by
  rw [Finset.sum_eq_multiset_sum]; rw [divisors_filter_squarefree h0]; rw [Multiset.map_map]; rw [Finset.sum_eq_multiset_sum]
  rfl

Depends on / 依赖: Finset, Finset.sum_eq_multiset_sum, Multiset, Multiset.map_map, divisors_filter_squarefree, map_map, sum_eq_multiset_sum
-/
theorem sum_divisors_filter_squarefree {n : Nat} (h0 : n != 0) {α : Type*} [AddCommMonoid α]
    {f : Nat -> α} :
    ∑ d in n.divisors with Squarefree d, f d =
      ∑ i in (UniqueFactorizationMonoid.normalizedFactors n).toFinset.powerset, f i.val.prod := by
  rw [Finset.sum_eq_multiset_sum]; rw [divisors_filter_squarefree h0]; rw [Multiset.map_map]; rw [Finset.sum_eq_multiset_sum]
  rfl

/--
theorem `sq_mul_squarefree_of_pos` / 定理 `sq_mul_squarefree_of_pos`

English:
theorem sq_mul_squarefree_of_pos
  given: {n : Nat} (hn : 0 < n)
  proof: by
  classical
  set S := {s in range (n + 1) | s ∣ n ∧ exists x, s = x ^ 2}
  have hSne : S.Nonempty := by
    use 1
    have h1 : 0 < n ∧ exists x : Nat, 1 = x ^ 2 := ⟨hn, ⟨1, (one_pow 2).symm⟩⟩
    simp [S, h1]
  let s := Finset.max' S hSne
  have hs : s in S := Finset.max'_mem S hSne
  simp only

中文:
定理 sq_mul_squarefree_of_pos
  条件: {n : 自然数} (hn : 0 < n)
  证明: by
  classical
  set S := {s in range (n + 1) | s ∣ n ∧ exists x, s = x ^ 2}
  have hSne : S.Nonempty := by
    use 1
    have h1 : 0 < n ∧ exists x : Nat, 1 = x ^ 2 := ⟨hn, ⟨1, (one_pow 2).symm⟩⟩
    simp [S, h1]
  let s := Finset.max' S hSne
  have hs : s in S := Finset.max'_mem S hSne
  simp only

Depends on / 依赖: CanonicallyOrderedAdd, CanonicallyOrderedAdd.mul_pos.mp, Finset, Finset.max, Finset.mem_filter, Finset.mem_range, Nonempty, S.Nonempty, _mem, classical, mem_filter, mem_range, mul_pos, one_pow, pow_pos_iff, two_ne_z
-/
theorem sq_mul_squarefree_of_pos {n : Nat} (hn : 0 < n) :
    exists a b : Nat, 0 < a ∧ 0 < b ∧ b ^ 2 * a = n ∧ Squarefree a := by
  classical
  set S := {s in range (n + 1) | s ∣ n ∧ exists x, s = x ^ 2}
  have hSne : S.Nonempty := by
    use 1
    have h1 : 0 < n ∧ exists x : Nat, 1 = x ^ 2 := ⟨hn, ⟨1, (one_pow 2).symm⟩⟩
    simp [S, h1]
  let s := Finset.max' S hSne
  have hs : s in S := Finset.max'_mem S hSne
  simp only [S, Finset.mem_filter, Finset.mem_range] at hs
  obtain ⟨-, ⟨a, hsa⟩, ⟨b, hsb⟩⟩ := hs
  rw [hsa] at hn
  obtain ⟨hlts, hlta⟩ := CanonicallyOrderedAdd.mul_pos.mp hn
  rw [hsb] at hsa hn hlts
  refine ⟨a, b, hlta, (pow_pos_iff two_ne_zero).mp hlts, hsa.symm, ?_⟩
  rintro x ⟨y, hy⟩
  rw [Nat.isUnit_iff]
  by_contra hx
  refine Nat.lt_le_asymm ?_ (Finset.le_max' S ((b * x) ^ 2) ?_)
  · convert!
      lt_mul_of_one_lt_right hlts
        (one_lt_pow two_ne_zero (one_lt_iff_ne_zero_and_ne_one.mpr ⟨fun h => by simp_all, hx⟩))
    using 1
    rw [mul_pow]
  · simp_rw [S, hsa, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.lt_succ_iff.mpr (le_of_dvd hn ?_), ?_, ⟨b * x, rfl⟩⟩ <;> use y <;> rw [hy] <;> ring

/--
theorem `sq_mul_squarefree_of_pos'` / 定理 `sq_mul_squarefree_of_pos'`

English:
theorem sq_mul_squarefree_of_pos'
  given: {n : Nat} (h : 0 < n)
  proof: by
  obtain ⟨a₁, b₁, ha₁, hb₁, hab₁, hab₂⟩ := sq_mul_squarefree_of_pos h
  refine ⟨a₁.pred, b₁.pred, ?_, ?_⟩ <;> simpa only [add_one, succ_pred_eq_of_pos, ha₁, hb₁]

中文:
定理 sq_mul_squarefree_of_pos'
  条件: {n : 自然数} (h : 0 < n)
  证明: by
  obtain ⟨a₁, b₁, ha₁, hb₁, hab₁, hab₂⟩ := sq_mul_squarefree_of_pos h
  refine ⟨a₁.pred, b₁.pred, ?_, ?_⟩ <;> simpa only [add_one, succ_pred_eq_of_pos, ha₁, hb₁]

Depends on / 依赖: add_one, sq_mul_squarefree_of_pos, succ_pred_eq_of_pos
-/
theorem sq_mul_squarefree_of_pos' {n : Nat} (h : 0 < n) :
    exists a b : Nat, (b + 1) ^ 2 * (a + 1) = n ∧ Squarefree (a + 1) := by
  obtain ⟨a₁, b₁, ha₁, hb₁, hab₁, hab₂⟩ := sq_mul_squarefree_of_pos h
  refine ⟨a₁.pred, b₁.pred, ?_, ?_⟩ <;> simpa only [add_one, succ_pred_eq_of_pos, ha₁, hb₁]

/--
theorem `sq_mul_squarefree` / 定理 `sq_mul_squarefree`

English:
theorem sq_mul_squarefree
  given: (n : Nat)
  statement: exists a b : Nat, b ^ 2 * a = n ∧ Squarefree a
  proof: by
  rcases n with - | n
  · exact ⟨1, 0, by simp, squarefree_one⟩
  · obtain ⟨a, b, -, -, h₁, h₂⟩ := sq_mul_squarefree_of_pos (succ_pos n)
    exact ⟨a, b, h₁, h₂⟩

中文:
定理 sq_mul_squarefree
  条件: (n : 自然数)
  结论: 存在 a b : 自然数, b ^ 2 * a = n ∧ Squarefree a
  证明: by
  rcases n with - | n
  · exact ⟨1, 0, by simp, squarefree_one⟩
  · obtain ⟨a, b, -, -, h₁, h₂⟩ := sq_mul_squarefree_of_pos (succ_pos n)
    exact ⟨a, b, h₁, h₂⟩

Depends on / 依赖: sq_mul_squarefree_of_pos, squarefree_one, succ_pos
-/
theorem sq_mul_squarefree (n : Nat) : exists a b : Nat, b ^ 2 * a = n ∧ Squarefree a := by
  rcases n with - | n
  · exact ⟨1, 0, by simp, squarefree_one⟩
  · obtain ⟨a, b, -, -, h₁, h₂⟩ := sq_mul_squarefree_of_pos (succ_pos n)
    exact ⟨a, b, h₁, h₂⟩

/--
theorem `squarefree_mul` / 定理 `squarefree_mul`

English:
theorem squarefree_mul
  given: {m n : Nat} (hmn : m.Coprime n)
  proof: by
  simp [squarefree_mul_iff, Nat.coprime_iff_isRelPrime.mp hmn]

中文:
定理 squarefree_mul
  条件: {m n : 自然数} (hmn : m.Coprime n)
  证明: by
  simp [squarefree_mul_iff, Nat.coprime_iff_isRelPrime.mp hmn]

Depends on / 依赖: Finite, Finite.of_injective, Fintype, Fintype.ofFinite, Nat.coprime_iff_isRelPrime.mp, algebraMap, bijective_frobeniusAlgEquivOfAlgebraic_pow, coprime_iff_isRelPrime, frobeniusAlgEquivOfAlgebraic, injective, ofFinite, of_injective, squarefree_mul_iff
-/
theorem squarefree_mul {m n : Nat} (hmn : m.Coprime n) :
    Squarefree (m * n) ↔ Squarefree m ∧ Squarefree n := by
  simp [squarefree_mul_iff, Nat.coprime_iff_isRelPrime.mp hmn]

/--
theorem `coprime_of_squarefree_mul` / 定理 `coprime_of_squarefree_mul`

English:
theorem coprime_of_squarefree_mul
  given: {m n : Nat} (h : Squarefree (m * n))
  statement: m.Coprime n
  proof: coprime_of_dvd fun p hp hm hn => squarefree_iff_prime_squarefree.mp h p hp (mul_dvd_mul hm hn)

中文:
定理 coprime_of_squarefree_mul
  条件: {m n : 自然数} (h : Squarefree (m * n))
  结论: m.Coprime n
  证明: coprime_of_dvd fun p hp hm hn => squarefree_iff_prime_squarefree.mp h p hp (mul_dvd_mul hm hn)

Depends on / 依赖: coprime_of_dvd, mul_dvd_mul, squarefree_iff_prime_squarefree, squarefree_iff_prime_squarefree.mp
-/
theorem coprime_of_squarefree_mul {m n : Nat} (h : Squarefree (m * n)) : m.Coprime n :=
  coprime_of_dvd fun p hp hm hn => squarefree_iff_prime_squarefree.mp h p hp (mul_dvd_mul hm hn)

/--
theorem `squarefree_mul_iff` / 定理 `squarefree_mul_iff`

English:
theorem squarefree_mul_iff
  given: {m n : Nat}
  proof: by
  rw [_root_.squarefree_mul_iff]; rw [Nat.coprime_iff_isRelPrime]

中文:
定理 squarefree_mul_iff
  条件: {m n : 自然数}
  证明: by
  rw [_root_.squarefree_mul_iff]; rw [Nat.coprime_iff_isRelPrime]

Depends on / 依赖: Nat.coprime_iff_isRelPrime, _root_, _root_.squarefree_mul_iff, coprime_iff_isRelPrime, squarefree_mul_iff
-/
theorem squarefree_mul_iff {m n : Nat} :
    Squarefree (m * n) ↔ m.Coprime n ∧ Squarefree m ∧ Squarefree n := by
  rw [_root_.squarefree_mul_iff]; rw [Nat.coprime_iff_isRelPrime]

/--
lemma `coprime_div_gcd_of_squarefree` / 引理 `coprime_div_gcd_of_squarefree`

English:
lemma coprime_div_gcd_of_squarefree
  given: (hm : Squarefree m) (hn : n != 0)
  statement: Coprime (m / gcd m n) n
  proof: by
  have : Coprime (m / gcd m n) (gcd m n) :=
coprime_of_squarefree_mul by simpa [Nat.div_mul_cancel, gcd_dvd_left]
  simpa [Nat.div_mul_cancel, gcd_dvd_right] using
    (coprime_div_gcd_div_gcd (m := m) (gcd_ne_zero_right hn).bot_lt).mul_right this

中文:
引理 coprime_div_gcd_of_squarefree
  条件: (hm : Squarefree m) (hn : n != 0)
  结论: Coprime (m / gcd m n) n
  证明: by
  have : Coprime (m / gcd m n) (gcd m n) :=
coprime_of_squarefree_mul by simpa [Nat.div_mul_cancel, gcd_dvd_left]
  simpa [Nat.div_mul_cancel, gcd_dvd_right] using
    (coprime_div_gcd_div_gcd (m := m) (gcd_ne_zero_right hn).bot_lt).mul_right this

Depends on / 依赖: Coprime, Nat.div_mul_cancel, bot_lt, coprime_div_gcd_div_gcd, coprime_of_squarefree_mul, div_mul_cancel, gcd_dvd_left, gcd_dvd_right, gcd_ne_zero_right, mul_right
-/
lemma coprime_div_gcd_of_squarefree (hm : Squarefree m) (hn : n != 0) : Coprime (m / gcd m n) n := by
  have : Coprime (m / gcd m n) (gcd m n) :=
coprime_of_squarefree_mul by simpa [Nat.div_mul_cancel, gcd_dvd_left]
  simpa [Nat.div_mul_cancel, gcd_dvd_right] using
    (coprime_div_gcd_div_gcd (m := m) (gcd_ne_zero_right hn).bot_lt).mul_right this

/--
lemma `prod_primeFactors_of_squarefree` / 引理 `prod_primeFactors_of_squarefree`

English:
lemma prod_primeFactors_of_squarefree
  given: (hn : Squarefree n)
  statement: ∏ p in n.primeFactors, p = n
  proof: by
  rw [← toFinset_factors]; rw [List.prod_toFinset _ hn.nodup_primeFactorsList]; rw [List.map_id']; rw [Nat.prod_primeFactorsList hn.ne_zero]

中文:
引理 prod_primeFactors_of_squarefree
  条件: (hn : Squarefree n)
  结论: ∏ p in n.primeFactors, p = n
  证明: by
  rw [← toFinset_factors]; rw [List.prod_toFinset _ hn.nodup_primeFactorsList]; rw [List.map_id']; rw [Nat.prod_primeFactorsList hn.ne_zero]

Depends on / 依赖: List.map_id, List.prod_toFinset, Nat.prod_primeFactorsList, hn.ne_zero, hn.nodup_primeFactorsList, map_id, ne_zero, nodup_primeFactorsList, prod_primeFactorsList, prod_toFinset, toFinset_factors
-/
lemma prod_primeFactors_of_squarefree (hn : Squarefree n) : ∏ p in n.primeFactors, p = n := by
  rw [← toFinset_factors]; rw [List.prod_toFinset _ hn.nodup_primeFactorsList]; rw [List.map_id']; rw [Nat.prod_primeFactorsList hn.ne_zero]

/--
lemma `primeFactors_prod` / 引理 `primeFactors_prod`

English:
lemma primeFactors_prod
  given: (hs : forall p in s, p.Prime)
  statement: primeFactors (∏ p in s, p) = s
  proof: by
  have hn : ∏ p in s, p != 0 := prod_ne_zero_iff.2 fun p hp => (hs _ hp).ne_zero
  ext p
  rw [mem_primeFactors_of_ne_zero hn]; rw [and_congr_right (fun hp => hp.prime.dvd_finsetProd_iff _)]
  refine ⟨?_, fun hp => ⟨hs _ hp, _, hp, dvd_rfl⟩⟩
  rintro ⟨hp, q, hq, hpq⟩
  rwa [← ((hs _ hq).dvd_iff_e

中文:
引理 primeFactors_prod
  条件: (hs : 对任意 p in s, p.Prime)
  结论: primeFactors (∏ p in s, p) = s
  证明: by
  have hn : ∏ p in s, p != 0 := prod_ne_zero_iff.2 fun p hp => (hs _ hp).ne_zero
  ext p
  rw [mem_primeFactors_of_ne_zero hn]; rw [and_congr_right (fun hp => hp.prime.dvd_finsetProd_iff _)]
  refine ⟨?_, fun hp => ⟨hs _ hp, _, hp, dvd_rfl⟩⟩
  rintro ⟨hp, q, hq, hpq⟩
  rwa [← ((hs _ hq).dvd_iff_e

Depends on / 依赖: and_congr_right, dvd_finsetProd_iff, dvd_iff_eq, dvd_rfl, hp.ne_one, hp.prime.dvd_finsetProd_iff, mem_primeFactors_of_ne_zero, ne_one, ne_zero, prod_ne_zero_iff
-/
lemma primeFactors_prod (hs : forall p in s, p.Prime) : primeFactors (∏ p in s, p) = s := by
  have hn : ∏ p in s, p != 0 := prod_ne_zero_iff.2 fun p hp => (hs _ hp).ne_zero
  ext p
  rw [mem_primeFactors_of_ne_zero hn]; rw [and_congr_right (fun hp => hp.prime.dvd_finsetProd_iff _)]
  refine ⟨?_, fun hp => ⟨hs _ hp, _, hp, dvd_rfl⟩⟩
  rintro ⟨hp, q, hq, hpq⟩
  rwa [← ((hs _ hq).dvd_iff_eq hp.ne_one).1 hpq]

/--
theorem `primeFactors_prod_primeFactors` / 定理 `primeFactors_prod_primeFactors`

English:
theorem primeFactors_prod_primeFactors
  given: (n : Nat)
  proof: .left primeFactors_prod fun _ hp => n.mem_primeFactors.mp hp

中文:
定理 primeFactors_prod_primeFactors
  条件: (n : 自然数)
  证明: .left primeFactors_prod fun _ hp => n.mem_primeFactors.mp hp

Depends on / 依赖: mem_primeFactors, n.mem_primeFactors.mp, primeFactors_prod
-/
theorem primeFactors_prod_primeFactors (n : Nat) :
    (∏ p in n.primeFactors, p).primeFactors = n.primeFactors :=
.left primeFactors_prod fun _ hp => n.mem_primeFactors.mp hp

/--
theorem `prod_primeFactors_dvd_iff` / 定理 `prod_primeFactors_dvd_iff`

English:
theorem prod_primeFactors_dvd_iff
  given: {n k : Nat} (hk : k != 0)
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · grw [← Nat.primeFactors_mono h hk, primeFactors_prod_primeFactors]
  · grw [← k.prod_primeFactors_dvd, Finset.prod_dvd_prod_of_subset _ _ _ h]

中文:
定理 prod_primeFactors_dvd_iff
  条件: {n k : 自然数} (hk : k != 0)
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · grw [← Nat.primeFactors_mono h hk, primeFactors_prod_primeFactors]
  · grw [← k.prod_primeFactors_dvd, Finset.prod_dvd_prod_of_subset _ _ _ h]

Depends on / 依赖: Finset, Finset.prod_dvd_prod_of_subset, Nat.primeFactors_mono, k.prod_primeFactors_dvd, primeFactors_mono, primeFactors_prod_primeFactors, prod_dvd_prod_of_subset, prod_primeFactors_dvd
-/
theorem prod_primeFactors_dvd_iff {n k : Nat} (hk : k != 0) :
    (∏ p in n.primeFactors, p) ∣ k ↔ n.primeFactors subseteq k.primeFactors := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · grw [← Nat.primeFactors_mono h hk, primeFactors_prod_primeFactors]
  · grw [← k.prod_primeFactors_dvd, Finset.prod_dvd_prod_of_subset _ _ _ h]

/--
lemma `primeFactors_div_gcd` / 引理 `primeFactors_div_gcd`

English:
lemma primeFactors_div_gcd
  given: (hm : Squarefree m) (hn : n != 0)
  proof: by
  ext p
  have : m / m.gcd n != 0 := by simp [gcd_ne_zero_right hn, gcd_le_left _ hm.ne_zero.bot_lt]
  simp only [mem_primeFactors, ne_eq, this, not_false_eq_true, and_true, not_and, mem_sdiff,
    hm.ne_zero, hn, dvd_div_iff_mul_dvd (gcd_dvd_left _ _)]
refine ⟨fun hp => ⟨⟨hp.1, dvd_of_mul_left_d

中文:
引理 primeFactors_div_gcd
  条件: (hm : Squarefree m) (hn : n != 0)
  证明: by
  ext p
  have : m / m.gcd n != 0 := by simp [gcd_ne_zero_right hn, gcd_le_left _ hm.ne_zero.bot_lt]
  simp only [mem_primeFactors, ne_eq, this, not_false_eq_true, and_true, not_and, mem_sdiff,
    hm.ne_zero, hn, dvd_div_iff_mul_dvd (gcd_dvd_left _ _)]
refine ⟨fun hp => ⟨⟨hp.1, dvd_of_mul_left_d

Depends on / 依赖: Coprime, Coprime.mul_dvd_of_dvd_of_dvd, and_true, bot_lt, coprim, dvd_div_iff_mul_dvd, dvd_gcd, dvd_of_mul_left_dvd, gcd_dvd_left, gcd_le_left, gcd_ne_zero_right, hm.ne_zero, hm.ne_zero.bot_lt, m.gcd, mem_primeFactors, mem_sdiff, mul_dvd_mul_right, mul_dvd_of_dvd_of_dvd, ne_eq, ne_zero
-/
lemma primeFactors_div_gcd (hm : Squarefree m) (hn : n != 0) :
    primeFactors (m / m.gcd n) = primeFactors m \ primeFactors n := by
  ext p
  have : m / m.gcd n != 0 := by simp [gcd_ne_zero_right hn, gcd_le_left _ hm.ne_zero.bot_lt]
  simp only [mem_primeFactors, ne_eq, this, not_false_eq_true, and_true, not_and, mem_sdiff,
    hm.ne_zero, hn, dvd_div_iff_mul_dvd (gcd_dvd_left _ _)]
refine ⟨fun hp => ⟨⟨hp.1, dvd_of_mul_left_dvd hp.2⟩, fun _ hpn => hp.1.not_isUnit hm _
    (mul_dvd_mul_right (dvd_gcd (dvd_of_mul_left_dvd hp.2) hpn) _).trans hp.2⟩, fun hp =>
      ⟨hp.1.1, Coprime.mul_dvd_of_dvd_of_dvd ?_ (gcd_dvd_left _ _) hp.1.2⟩⟩
  rw [coprime_comm]; rw [hp.1.1.coprime_iff_not_dvd]
exact fun hpn => hp.2 hp.1.1 hpn.trans gcd_dvd_right _ _

/--
lemma `prod_primeFactors_invOn_squarefree` / 引理 `prod_primeFactors_invOn_squarefree`

English:
lemma prod_primeFactors_invOn_squarefree
  proof: ⟨fun _s => primeFactors_prod, fun _n => prod_primeFactors_of_squarefree⟩

中文:
引理 prod_primeFactors_invOn_squarefree
  证明: ⟨fun _s => primeFactors_prod, fun _n => prod_primeFactors_of_squarefree⟩

Depends on / 依赖: primeFactors_prod, prod_primeFactors_of_squarefree
-/
lemma prod_primeFactors_invOn_squarefree :
    Set.InvOn (fun n : Nat => (factorization n).support) (fun s => ∏ p in s, p)
      {s | forall p in s, p.Prime} {n | Squarefree n} :=
  ⟨fun _s => primeFactors_prod, fun _n => prod_primeFactors_of_squarefree⟩

/--
theorem `prod_primeFactors_sdiff_of_squarefree` / 定理 `prod_primeFactors_sdiff_of_squarefree`

English:
theorem prod_primeFactors_sdiff_of_squarefree
  statement: {n : Nat} (hn : Squarefree n) {t : Finset Nat}
  proof: by
refine symm Nat.div_eq_of_eq_mul_left (Finset.prod_pos
    fun p hp => (prime_of_mem_primeFactorsList (List.mem_toFinset.mp (ht hp))).pos) ?_
  rw [Finset.prod_sdiff ht]; rw [prod_primeFactors_of_squarefree hn]

中文:
定理 prod_primeFactors_sdiff_of_squarefree
  结论: {n : 自然数} (hn : Squarefree n) {t : Finset 自然数}
  证明: by
refine symm Nat.div_eq_of_eq_mul_left (Finset.prod_pos
    fun p hp => (prime_of_mem_primeFactorsList (List.mem_toFinset.mp (ht hp))).pos) ?_
  rw [Finset.prod_sdiff ht]; rw [prod_primeFactors_of_squarefree hn]

Depends on / 依赖: Finset, Finset.prod_pos, Finset.prod_sdiff, List.mem_toFinset.mp, Nat.div_eq_of_eq_mul_left, div_eq_of_eq_mul_left, mem_toFinset, prime_of_mem_primeFactorsList, prod_pos, prod_primeFactors_of_squarefree, prod_sdiff
-/
theorem prod_primeFactors_sdiff_of_squarefree {n : Nat} (hn : Squarefree n) {t : Finset Nat}
    (ht : t subseteq n.primeFactors) :
    ∏ a in (n.primeFactors \ t), a = n / ∏ a in t, a := by
refine symm Nat.div_eq_of_eq_mul_left (Finset.prod_pos
    fun p hp => (prime_of_mem_primeFactorsList (List.mem_toFinset.mp (ht hp))).pos) ?_
  rw [Finset.prod_sdiff ht]; rw [prod_primeFactors_of_squarefree hn]

end Nat

-- Porting note: comment out NormNum tactic, to be moved to another file.
/-

/-! ### Square-free prover -/


open NormNum

namespace Tactic

namespace NormNum

/--
Definition of `SquarefreeHelper` / `SquarefreeHelper` 的定义

English:
definition SquarefreeHelper
  signature: (n k : Nat)
  body: 0 < k -> (forall m, Nat.Prime m -> m ∣ bit1 n -> bit1 k <= m) -> Squarefree (bit1 n)

中文:
定义 SquarefreeHelper
  签名: (n k : 自然数)
  定义体: 0 < k -> (forall m, Nat.Prime m -> m ∣ bit1 n -> bit1 k <= m) -> Squarefree (bit1 n)

Depends on / 依赖: Nat.Prime, Squarefree
-/
def SquarefreeHelper (n k : Nat) : Prop :=
  0 < k -> (forall m, Nat.Prime m -> m ∣ bit1 n -> bit1 k <= m) -> Squarefree (bit1 n)

/--
theorem `squarefree_bit10` / 定理 `squarefree_bit10`

English:
theorem squarefree_bit10
  given: (n : Nat) (h : SquarefreeHelper n 1)
  statement: Squarefree (bit0 (bit1 n))
  proof: by
  refine' @Nat.minSqFacProp_div _ _ Nat.prime_two two_dvd_bit0 _ none _
  · rw [bit0_eq_two_mul (bit1 n), mul_dvd_mul_iff_left (two_ne_zero' Nat)]
    exact Nat.not_two_dvd_bit1 _
  · rw [bit0_eq_two_mul, Nat.mul_div_right _ (by decide : 0 < 2)]
    refine' h (by decide) fun p pp dp => Nat.succ_l

中文:
定理 squarefree_bit10
  条件: (n : 自然数) (h : SquarefreeHelper n 1)
  结论: Squarefree (bit0 (bit1 n))
  证明: by
  refine' @Nat.minSqFacProp_div _ _ Nat.prime_two two_dvd_bit0 _ none _
  · rw [bit0_eq_two_mul (bit1 n), mul_dvd_mul_iff_left (two_ne_zero' Nat)]
    exact Nat.not_two_dvd_bit1 _
  · rw [bit0_eq_two_mul, Nat.mul_div_right _ (by decide : 0 < 2)]
    refine' h (by decide) fun p pp dp => Nat.succ_l

Depends on / 依赖: Nat.minSqFacProp_div, Nat.mul_div_right, Nat.not_two_dvd_bit1, Nat.prime_two, Nat.succ_le_of_lt, bit0_eq_two_mul, lt_of_le_of_ne, minSqFacProp_div, mul_div_right, mul_dvd_mul_iff_left, not_two_dvd_bit1, pp.two_le, prime_two, succ_le_of_lt, two_dvd_bit0, two_le, two_ne_zero
-/
theorem squarefree_bit10 (n : Nat) (h : SquarefreeHelper n 1) : Squarefree (bit0 (bit1 n)) := by
  refine' @Nat.minSqFacProp_div _ _ Nat.prime_two two_dvd_bit0 _ none _
  · rw [bit0_eq_two_mul (bit1 n), mul_dvd_mul_iff_left (two_ne_zero' Nat)]
    exact Nat.not_two_dvd_bit1 _
  · rw [bit0_eq_two_mul, Nat.mul_div_right _ (by decide : 0 < 2)]
    refine' h (by decide) fun p pp dp => Nat.succ_le_of_lt (lt_of_le_of_ne pp.two_le _)
    rintro rfl
    exact Nat.not_two_dvd_bit1 _ dp

/--
theorem `squarefree_bit1` / 定理 `squarefree_bit1`

English:
theorem squarefree_bit1
  given: (n : Nat) (h : SquarefreeHelper n 1)
  statement: Squarefree (bit1 n)
  proof: by
  refine' h (by decide) fun p pp dp => Nat.succ_le_of_lt (lt_of_le_of_ne pp.two_le _)
  rintro rfl; exact Nat.not_two_dvd_bit1 _ dp

中文:
定理 squarefree_bit1
  条件: (n : 自然数) (h : SquarefreeHelper n 1)
  结论: Squarefree (bit1 n)
  证明: by
  refine' h (by decide) fun p pp dp => Nat.succ_le_of_lt (lt_of_le_of_ne pp.two_le _)
  rintro rfl; exact Nat.not_two_dvd_bit1 _ dp

Depends on / 依赖: Nat.not_two_dvd_bit1, Nat.succ_le_of_lt, lt_of_le_of_ne, not_two_dvd_bit1, pp.two_le, succ_le_of_lt, two_le
-/
theorem squarefree_bit1 (n : Nat) (h : SquarefreeHelper n 1) : Squarefree (bit1 n) := by
  refine' h (by decide) fun p pp dp => Nat.succ_le_of_lt (lt_of_le_of_ne pp.two_le _)
  rintro rfl; exact Nat.not_two_dvd_bit1 _ dp

/--
theorem `squarefree_helper_0` / 定理 `squarefree_helper_0`

English:
theorem squarefree_helper_0
  given: {k} (k0 : 0 < k) {p : Nat} (pp : Nat.Prime p) (h : bit1 k <= p)
  proof: by
  rcases lt_or_eq_of_le h with ((hp : _ + 1 <= _) | hp)
  · rw [bit1, bit0_eq_two_mul] at hp
    change 2 * (_ + 1) <= _ at hp
    rw [bit1]; rw [bit0_eq_two_mul]
    refine' Or.inl (lt_of_le_of_ne hp _)
    rintro rfl
    exact Nat.not_prime_mul (by decide) (lt_add_of_pos_left _ k0) pp
  · exact

中文:
定理 squarefree_helper_0
  条件: {k} (k0 : 0 < k) {p : 自然数} (pp : 自然数.Prime p) (h : bit1 k <= p)
  证明: by
  rcases lt_or_eq_of_le h with ((hp : _ + 1 <= _) | hp)
  · rw [bit1, bit0_eq_two_mul] at hp
    change 2 * (_ + 1) <= _ at hp
    rw [bit1]; rw [bit0_eq_two_mul]
    refine' Or.inl (lt_of_le_of_ne hp _)
    rintro rfl
    exact Nat.not_prime_mul (by decide) (lt_add_of_pos_left _ k0) pp
  · exact

Depends on / 依赖: Nat.not_prime_mul, Or.inl, Or.inr, bit0_eq_two_mul, lt_add_of_pos_left, lt_of_le_of_ne, lt_or_eq_of_le, not_prime_mul
-/
theorem squarefree_helper_0 {k} (k0 : 0 < k) {p : Nat} (pp : Nat.Prime p) (h : bit1 k <= p) :
    bit1 (k + 1) <= p ∨ bit1 k = p := by
  rcases lt_or_eq_of_le h with ((hp : _ + 1 <= _) | hp)
  · rw [bit1, bit0_eq_two_mul] at hp
    change 2 * (_ + 1) <= _ at hp
    rw [bit1]; rw [bit0_eq_two_mul]
    refine' Or.inl (lt_of_le_of_ne hp _)
    rintro rfl
    exact Nat.not_prime_mul (by decide) (lt_add_of_pos_left _ k0) pp
  · exact Or.inr hp

/--
theorem `squarefreeHelper_1` / 定理 `squarefreeHelper_1`

English:
theorem squarefreeHelper_1
  statement: (n k k' : Nat) (e : k + 1 = k')
  proof: fun k0 ih => by
  subst e
  refine' H (Nat.succ_pos _) fun p pp dp => _
  refine' (squarefree_helper_0 k0 pp (ih p pp dp)).resolve_right fun hp => _
  subst hp; cases hk pp dp

中文:
定理 squarefreeHelper_1
  结论: (n k k' : 自然数) (e : k + 1 = k')
  证明: fun k0 ih => by
  subst e
  refine' H (Nat.succ_pos _) fun p pp dp => _
  refine' (squarefree_helper_0 k0 pp (ih p pp dp)).resolve_right fun hp => _
  subst hp; cases hk pp dp

Depends on / 依赖: Nat.succ_pos, resolve_right, squarefree_helper_0, succ_pos
-/
theorem squarefreeHelper_1 (n k k' : Nat) (e : k + 1 = k')
    (hk : Nat.Prime (bit1 k) -> ¬bit1 k ∣ bit1 n) (H : SquarefreeHelper n k') :
    SquarefreeHelper n k := fun k0 ih => by
  subst e
  refine' H (Nat.succ_pos _) fun p pp dp => _
  refine' (squarefree_helper_0 k0 pp (ih p pp dp)).resolve_right fun hp => _
  subst hp; cases hk pp dp

/--
theorem `squarefreeHelper_2` / 定理 `squarefreeHelper_2`

English:
theorem squarefreeHelper_2
  statement: (n k k' c : Nat) (e : k + 1 = k') (hc : bit1 n % bit1 k = c) (c0 : 0 < c)
  proof: by
  refine' squarefree_helper_1 _ _ _ e (fun _ => _) h
  refine' mt _ (ne_of_gt c0); intro e₁
  rwa [← hc, ← Nat.dvd_iff_mod_eq_zero]

中文:
定理 squarefreeHelper_2
  结论: (n k k' c : 自然数) (e : k + 1 = k') (hc : bit1 n % bit1 k = c) (c0 : 0 < c)
  证明: by
  refine' squarefree_helper_1 _ _ _ e (fun _ => _) h
  refine' mt _ (ne_of_gt c0); intro e₁
  rwa [← hc, ← Nat.dvd_iff_mod_eq_zero]

Depends on / 依赖: Nat.dvd_iff_mod_eq_zero, dvd_iff_mod_eq_zero, ne_of_gt, squarefree_helper_1
-/
theorem squarefreeHelper_2 (n k k' c : Nat) (e : k + 1 = k') (hc : bit1 n % bit1 k = c) (c0 : 0 < c)
    (h : SquarefreeHelper n k') : SquarefreeHelper n k := by
  refine' squarefree_helper_1 _ _ _ e (fun _ => _) h
  refine' mt _ (ne_of_gt c0); intro e₁
  rwa [← hc, ← Nat.dvd_iff_mod_eq_zero]

/--
theorem `squarefreeHelper_3` / 定理 `squarefreeHelper_3`

English:
theorem squarefreeHelper_3
  statement: (n n' k k' c : Nat) (e : k + 1 = k') (hn' : bit1 n' * bit1 k = bit1 n)
  proof: fun k0 ih => by
  subst e
  have k0' : 0 < bit1 k := bit1_pos (Nat.zero_le _)
  have dn' : bit1 n' ∣ bit1 n := ⟨_, hn'.symm⟩
  have dk : bit1 k ∣ bit1 n := ⟨_, ((mul_comm _ _).trans hn').symm⟩
  have : bit1 n / bit1 k = bit1 n' := by rw [← hn', Nat.mul_div_cancel _ k0']
  have k2 : 2 <= bit1 k := Na

中文:
定理 squarefreeHelper_3
  结论: (n n' k k' c : 自然数) (e : k + 1 = k') (hn' : bit1 n' * bit1 k = bit1 n)
  证明: fun k0 ih => by
  subst e
  have k0' : 0 < bit1 k := bit1_pos (Nat.zero_le _)
  have dn' : bit1 n' ∣ bit1 n := ⟨_, hn'.symm⟩
  have dk : bit1 k ∣ bit1 n := ⟨_, ((mul_comm _ _).trans hn').symm⟩
  have : bit1 n / bit1 k = bit1 n' := by rw [← hn', Nat.mul_div_cancel _ k0']
  have k2 : 2 <= bit1 k := Na

Depends on / 依赖: Nat.minFac_dvd, Nat.minFac_le, Nat.minFac_prime, Nat.mul_div_cancel, Nat.prime_def_minFac, Nat.succ_le_succ, Nat.zero_le, bit0_pos, bit1_pos, dvd_trans, le_antisymm, minFac_dvd, minFac_le, minFac_prime, mul_comm, mul_div_cancel, ne_of_gt, prime_def_minFac, succ_le_succ, zero_le
-/
theorem squarefreeHelper_3 (n n' k k' c : Nat) (e : k + 1 = k') (hn' : bit1 n' * bit1 k = bit1 n)
    (hc : bit1 n' % bit1 k = c) (c0 : 0 < c) (H : SquarefreeHelper n' k') : SquarefreeHelper n k :=
  fun k0 ih => by
  subst e
  have k0' : 0 < bit1 k := bit1_pos (Nat.zero_le _)
  have dn' : bit1 n' ∣ bit1 n := ⟨_, hn'.symm⟩
  have dk : bit1 k ∣ bit1 n := ⟨_, ((mul_comm _ _).trans hn').symm⟩
  have : bit1 n / bit1 k = bit1 n' := by rw [← hn', Nat.mul_div_cancel _ k0']
  have k2 : 2 <= bit1 k := Nat.succ_le_succ (bit0_pos k0)
  have pk : (bit1 k).Prime := by
    refine' Nat.prime_def_minFac.2 ⟨k2, le_antisymm (Nat.minFac_le k0') _⟩
    exact ih _ (Nat.minFac_prime (ne_of_gt k2)) (dvd_trans (Nat.minFac_dvd _) dk)
  have dkk' : ¬bit1 k ∣ bit1 n' := by
    rw [Nat.dvd_iff_mod_eq_zero]; rw [hc]
    exact ne_of_gt c0
  have dkk : ¬bit1 k * bit1 k ∣ bit1 n := by rwa [← Nat.dvd_div_iff_mul_dvd dk, this]
  refine' @Nat.minSqFacProp_div _ _ pk dk dkk none _
  rw [this]
  refine' H (Nat.succ_pos _) fun p pp dp => _
  refine' (squarefree_helper_0 k0 pp (ih p pp <| dvd_trans dp dn')).resolve_right fun e => _
  subst e
  contradiction

/--
theorem `squarefreeHelper_4` / 定理 `squarefreeHelper_4`

English:
theorem squarefreeHelper_4
  given: (n k k' : Nat) (e : bit1 k * bit1 k = k') (hd : bit1 n < k')
  proof: by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst n
    exact fun _ _ => squarefree_one
  subst e
  refine' fun k0 ih => Irreducible.squarefree (Nat.prime_def_le_sqrt.2 ⟨bit1_lt_bit1.2 h, _⟩)
  intro m m2 hm md
  obtain ⟨p, pp, hp⟩ := Nat.exists_prime_and_dvd (ne_of_gt m2)
  have :=
    (ih p pp

中文:
定理 squarefreeHelper_4
  条件: (n k k' : 自然数) (e : bit1 k * bit1 k = k') (hd : bit1 n < k')
  证明: by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst n
    exact fun _ _ => squarefree_one
  subst e
  refine' fun k0 ih => Irreducible.squarefree (Nat.prime_def_le_sqrt.2 ⟨bit1_lt_bit1.2 h, _⟩)
  intro m m2 hm md
  obtain ⟨p, pp, hp⟩ := Nat.exists_prime_and_dvd (ne_of_gt m2)
  have :=
    (ih p pp

Depends on / 依赖: Irreducible, Irreducible.squarefree, Nat.eq_zero_or_pos, Nat.exists_prime_and_dvd, Nat.le_of_dvd, Nat.le_sqrt, Nat.prime_def_le_sqrt, bit1_lt_bit1, dvd_trans, eq_zero_or_pos, exists_prime_and_dvd, le_of_dvd, le_sqrt, le_trans, lt_of_lt_of_le, ne_of_gt, not_le_of_gt, prime_def_le_sqrt, squarefree, squarefree_one
-/
theorem squarefreeHelper_4 (n k k' : Nat) (e : bit1 k * bit1 k = k') (hd : bit1 n < k') :
    SquarefreeHelper n k := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst n
    exact fun _ _ => squarefree_one
  subst e
  refine' fun k0 ih => Irreducible.squarefree (Nat.prime_def_le_sqrt.2 ⟨bit1_lt_bit1.2 h, _⟩)
  intro m m2 hm md
  obtain ⟨p, pp, hp⟩ := Nat.exists_prime_and_dvd (ne_of_gt m2)
  have :=
    (ih p pp (dvd_trans hp md)).trans
      (le_trans (Nat.le_of_dvd (lt_of_lt_of_le (by decide) m2) hp) hm)
  rw [Nat.le_sqrt] at this
  exact not_le_of_gt hd this

/--
theorem `not_squarefree_mul` / 定理 `not_squarefree_mul`

English:
theorem not_squarefree_mul
  given: (a aa b n : Nat) (ha : a * a = aa) (hb : aa * b = n) (h₁ : 1 < a)
  proof: by
  rw [← hb]; rw [← ha]
  exact fun H => ne_of_gt h₁ (Nat.isUnit_iff.1 <| H _ ⟨_, rfl⟩)

中文:
定理 not_squarefree_mul
  条件: (a aa b n : 自然数) (ha : a * a = aa) (hb : aa * b = n) (h₁ : 1 < a)
  证明: by
  rw [← hb]; rw [← ha]
  exact fun H => ne_of_gt h₁ (Nat.isUnit_iff.1 <| H _ ⟨_, rfl⟩)

Depends on / 依赖: Nat.isUnit_iff, isUnit_iff, ne_of_gt
-/
theorem not_squarefree_mul (a aa b n : Nat) (ha : a * a = aa) (hb : aa * b = n) (h₁ : 1 < a) :
    ¬Squarefree n := by
  rw [← hb]; rw [← ha]
  exact fun H => ne_of_gt h₁ (Nat.isUnit_iff.1 <| H _ ⟨_, rfl⟩)

/-- Given `e` a natural numeral and `a : ℕ` with `a^2 ∣ n`, return `⊢ ¬ Squarefree e`. -/
unsafe def prove_non_squarefree (e : expr) (n a : Nat) : tactic expr := do
  let ea := reflect a
  let eaa := reflect (a * a)
  let c ← mk_instance_cache q(Nat)
  let (c, p₁) ← prove_lt_nat c q(1) ea
  let b := n / (a * a)
  let eb := reflect b
  let (c, eaa, pa) ← prove_mul_nat c ea ea
  let (c, e', pb) ← prove_mul_nat c eaa eb
  guard (e' == e)
return q(@not_squarefree_mul).mk_app [ea, eaa, eb, e, pa, pb, p₁]

/-- Given `en`,`en1 := bit1 en`, `n1` the value of `en1`, `ek`,
  returns `⊢ squarefree_helper en ek`. -/
unsafe def prove_squarefree_aux :
    forall (ic : instance_cache) (en en1 : expr) (n1 : Nat) (ek : expr) (k : Nat), tactic expr
  | ic, en, en1, n1, ek, k => do
    let k1 := bit1 k
    let ek1 := q((bit1 : Nat -> Nat)).mk_app [ek]
    if n1 < k1 * k1 then do
        let (ic, ek', p₁) ← prove_mul_nat ic ek1 ek1
        let (ic, p₂) ← prove_lt_nat ic en1 ek'
pure q(squarefreeHelper_4).mk_app [en, ek, ek', p₁, p₂]
      else do
        let c := n1 % k1
        let k' := k + 1
        let ek' := reflect k'
        let (ic, p₁) ← prove_succ ic ek ek'
        if c = 0 then do
            let n1' := n1 / k1
            let n' := n1' / 2
            let en' := reflect n'
            let en1' := q((bit1 : Nat -> Nat)).mk_app [en']
            let (ic, _, pn') ← prove_mul_nat ic en1' ek1
            let c := n1' % k1
            guard (c != 0)
            let (ic, ec, pc) ← prove_div_mod ic en1' ek1 tt
            let (ic, p₀) ← prove_pos ic ec
            let p₂ ← prove_squarefree_aux ic en' en1' n1' ek' k'
pure q(squarefreeHelper_3).mk_app [en, en', ek, ek', ec, p₁, pn', pc, p₀, p₂]
          else do
            let (ic, ec, pc) ← prove_div_mod ic en1 ek1 tt
            let (ic, p₀) ← prove_pos ic ec
            let p₂ ← prove_squarefree_aux ic en en1 n1 ek' k'
pure q(squarefreeHelper_2).mk_app [en, ek, ek', ec, p₁, pc, p₀, p₂]

/-- Given `n > 0` a squarefree natural numeral, returns `⊢ Squarefree n`. -/
unsafe def prove_squarefree (en : expr) (n : Nat) : tactic expr :=
  match match_numeral en with
  | match_numeral_result.one => pure q(@squarefree_one Nat _)
  | match_numeral_result.bit0 en1 =>
    match match_numeral en1 with
    | match_numeral_result.one => pure q(Nat.squarefree_two)
    | match_numeral_result.bit1 en => do
      let ic ← mk_instance_cache q(Nat)
      let p ← prove_squarefree_aux ic en en1 (n / 2) q((1 : Nat)) 1
pure q(squarefree_bit10).mk_app [en, p]
    | _ => failed
  | match_numeral_result.bit1 en' => do
    let ic ← mk_instance_cache q(Nat)
    let p ← prove_squarefree_aux ic en' en n q((1 : Nat)) 1
pure q(squarefree_bit1).mk_app [en', p]
  | _ => failed

/-- Evaluates the `Squarefree` predicate on naturals. -/
@[norm_num]
unsafe def eval_squarefree : expr -> tactic (expr × expr)
  | q(@Squarefree Nat $(inst) $(e)) => do
    is_def_eq inst q(Nat.monoid)
    let n ← e.toNat
    match n with
      | 0 => false_intro q(@not_squarefree_zero Nat _ _)
      | 1 => true_intro q(@squarefree_one Nat _)
      | _ =>
        match n with
        | some d => prove_non_squarefree e n d >>= false_intro
        | none => prove_squarefree e n >>= true_intro
  | _ => failed

end NormNum

end Tactic

-/
