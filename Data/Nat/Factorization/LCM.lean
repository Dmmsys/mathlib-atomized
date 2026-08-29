/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Lemmas about `factorizationLCMLeft`

This file contains some lemmas about `factorizationLCMLeft`.
These were split from `Mathlib.Data.Nat.Factorization.Basic` to reduce transitive imports.
-/

public section

open Finset List Finsupp

namespace Nat

variable (a b)

/--
lemma `factorizationLCMLeft_zero_left` / 引理 `factorizationLCMLeft_zero_left`

English:
lemma factorizationLCMLeft_zero_left
  statement: factorizationLCMLeft 0 b = 1
  proof: by
  simp [factorizationLCMLeft]

中文:
引理 factorizationLCMLeft_zero_left
  结论: factorizationLCMLeft 0 b = 1
  证明: by
  simp [factorizationLCMLeft]
-/
@[simp] lemma factorizationLCMLeft_zero_left : factorizationLCMLeft 0 b = 1 := by
  simp [factorizationLCMLeft]

/--
lemma `factorizationLCMLeft_zero_right` / 引理 `factorizationLCMLeft_zero_right`

English:
lemma factorizationLCMLeft_zero_right
  statement: factorizationLCMLeft a 0 = 1
  proof: by
  simp [factorizationLCMLeft]

中文:
引理 factorizationLCMLeft_zero_right
  结论: factorizationLCMLeft a 0 = 1
  证明: by
  simp [factorizationLCMLeft]
-/
@[simp] lemma factorizationLCMLeft_zero_right : factorizationLCMLeft a 0 = 1 := by
  simp [factorizationLCMLeft]

/--
lemma `factorizationLCRight_zero_left` / 引理 `factorizationLCRight_zero_left`

English:
lemma factorizationLCRight_zero_left
  statement: factorizationLCMRight 0 b = 1
  proof: by
  simp [factorizationLCMRight]

中文:
引理 factorizationLCRight_zero_left
  结论: factorizationLCMRight 0 b = 1
  证明: by
  simp [factorizationLCMRight]
-/
@[simp] lemma factorizationLCRight_zero_left : factorizationLCMRight 0 b = 1 := by
  simp [factorizationLCMRight]

/--
lemma `factorizationLCMRight_zero_right` / 引理 `factorizationLCMRight_zero_right`

English:
lemma factorizationLCMRight_zero_right
  statement: factorizationLCMRight a 0 = 1
  proof: by
  simp [factorizationLCMRight]

中文:
引理 factorizationLCMRight_zero_right
  结论: factorizationLCMRight a 0 = 1
  证明: by
  simp [factorizationLCMRight]
-/
@[simp] lemma factorizationLCMRight_zero_right : factorizationLCMRight a 0 = 1 := by
  simp [factorizationLCMRight]

/--
lemma `factorizationLCMLeft_pos` / 引理 `factorizationLCMLeft_pos`

English:
lemma factorizationLCMLeft_pos
  statement: 0 < factorizationLCMLeft a b
  proof: by
  apply Nat.pos_of_ne_zero
  rw [factorizationLCMLeft]; rw [Finsupp.prod_ne_zero_iff]
  intro p _ H
  by_cases h : b.factorization p <= a.factorization p
  · simp only [h, reduceIte, pow_eq_zero_iff', ne_eq] at H
    simpa [H.1] using H.2
  · simp only [h, reduceIte, one_ne_zero] at H

中文:
引理 factorizationLCMLeft_pos
  结论: 0 < factorizationLCMLeft a b
  证明: by
  apply Nat.pos_of_ne_zero
  rw [factorizationLCMLeft]; rw [Finsupp.prod_ne_zero_iff]
  intro p _ H
  by_cases h : b.factorization p <= a.factorization p
  · simp only [h, reduceIte, pow_eq_zero_iff', ne_eq] at H
    simpa [H.1] using H.2
  · simp only [h, reduceIte, one_ne_zero] at H

Depends on / 依赖: Finsupp, Finsupp.prod_ne_zero_iff, Nat.pos_of_ne_zero, a.factorization, b.factorization, factorization, factorizationLCMLeft, ne_eq, one_ne_zero, pos_of_ne_zero, pow_eq_zero_iff, prod_ne_zero_iff, reduceIte
-/
lemma factorizationLCMLeft_pos : 0 < factorizationLCMLeft a b := by
  apply Nat.pos_of_ne_zero
  rw [factorizationLCMLeft]; rw [Finsupp.prod_ne_zero_iff]
  intro p _ H
  by_cases h : b.factorization p <= a.factorization p
  · simp only [h, reduceIte, pow_eq_zero_iff', ne_eq] at H
    simpa [H.1] using H.2
  · simp only [h, reduceIte, one_ne_zero] at H

/--
lemma `factorizationLCMRight_pos` / 引理 `factorizationLCMRight_pos`

English:
lemma factorizationLCMRight_pos
  statement: 0 < factorizationLCMRight a b
  proof: by
  apply Nat.pos_of_ne_zero
  rw [factorizationLCMRight]; rw [Finsupp.prod_ne_zero_iff]
  intro p _ H
  by_cases h : b.factorization p <= a.factorization p
  · simp only [h, reduceIte, reduceCtorEq] at H
  · simp only [h, ↓reduceIte, pow_eq_zero_iff', ne_eq] at H
    simpa [H.1] using H.2

中文:
引理 factorizationLCMRight_pos
  结论: 0 < factorizationLCMRight a b
  证明: by
  apply Nat.pos_of_ne_zero
  rw [factorizationLCMRight]; rw [Finsupp.prod_ne_zero_iff]
  intro p _ H
  by_cases h : b.factorization p <= a.factorization p
  · simp only [h, reduceIte, reduceCtorEq] at H
  · simp only [h, ↓reduceIte, pow_eq_zero_iff', ne_eq] at H
    simpa [H.1] using H.2

Depends on / 依赖: Finsupp, Finsupp.prod_ne_zero_iff, Nat.pos_of_ne_zero, a.factorization, b.factorization, factorization, factorizationLCMRight, ne_eq, pos_of_ne_zero, pow_eq_zero_iff, prod_ne_zero_iff, reduceCtorEq, reduceIte
-/
lemma factorizationLCMRight_pos : 0 < factorizationLCMRight a b := by
  apply Nat.pos_of_ne_zero
  rw [factorizationLCMRight]; rw [Finsupp.prod_ne_zero_iff]
  intro p _ H
  by_cases h : b.factorization p <= a.factorization p
  · simp only [h, reduceIte, reduceCtorEq] at H
  · simp only [h, ↓reduceIte, pow_eq_zero_iff', ne_eq] at H
    simpa [H.1] using H.2

/--
lemma `coprime_factorizationLCMLeft_factorizationLCMRight` / 引理 `coprime_factorizationLCMLeft_factorizationLCMRight`

English:
lemma coprime_factorizationLCMLeft_factorizationLCMRight
  proof: by
  rw [factorizationLCMLeft]; rw [factorizationLCMRight]
  refine coprime_prod_left_iff.mpr fun p hp => coprime_prod_right_iff.mpr fun q hq => ?_
  dsimp only; split_ifs with h h'
  any_goals simp only [coprime_one_right_eq_true, coprime_one_left_eq_true]
  refine coprime_pow_primes _ _ (prime_of_

中文:
引理 coprime_factorizationLCMLeft_factorizationLCMRight
  证明: by
  rw [factorizationLCMLeft]; rw [factorizationLCMRight]
  refine coprime_prod_left_iff.mpr fun p hp => coprime_prod_right_iff.mpr fun q hq => ?_
  dsimp only; split_ifs with h h'
  any_goals simp only [coprime_one_right_eq_true, coprime_one_left_eq_true]
  refine coprime_pow_primes _ _ (prime_of_

Depends on / 依赖: any_goals, contrapose, coprime_one_left_eq_true, coprime_one_right_eq_true, coprime_pow_primes, coprime_prod_left_iff, coprime_prod_left_iff.mpr, coprime_prod_right_iff, coprime_prod_right_iff.mpr, factorizationLCMLeft, factorizationLCMRight, prime_of_mem_primeFactors, split_ifs
-/
lemma coprime_factorizationLCMLeft_factorizationLCMRight :
    (factorizationLCMLeft a b).Coprime (factorizationLCMRight a b) := by
  rw [factorizationLCMLeft]; rw [factorizationLCMRight]
  refine coprime_prod_left_iff.mpr fun p hp => coprime_prod_right_iff.mpr fun q hq => ?_
  dsimp only; split_ifs with h h'
  any_goals simp only [coprime_one_right_eq_true, coprime_one_left_eq_true]
  refine coprime_pow_primes _ _ (prime_of_mem_primeFactors hp) (prime_of_mem_primeFactors hq) ?_
  contrapose h'; rwa [← h']

variable {a b}

/--
lemma `factorizationLCMLeft_mul_factorizationLCMRight` / 引理 `factorizationLCMLeft_mul_factorizationLCMRight`

English:
lemma factorizationLCMLeft_mul_factorizationLCMRight
  given: (ha : a != 0) (hb : b != 0)
  proof: by
  rw [← prod_factorization_pow_eq_self (lcm_ne_zero ha hb)]; rw [factorizationLCMLeft]; rw [factorizationLCMRight]; rw [← prod_mul]
  congr; ext p n; split_ifs <;> simp

中文:
引理 factorizationLCMLeft_mul_factorizationLCMRight
  条件: (ha : a != 0) (hb : b != 0)
  证明: by
  rw [← prod_factorization_pow_eq_self (lcm_ne_zero ha hb)]; rw [factorizationLCMLeft]; rw [factorizationLCMRight]; rw [← prod_mul]
  congr; ext p n; split_ifs <;> simp

Depends on / 依赖: factorizationLCMLeft, factorizationLCMRight, lcm_ne_zero, prod_factorization_pow_eq_self, prod_mul, split_ifs
-/
lemma factorizationLCMLeft_mul_factorizationLCMRight (ha : a != 0) (hb : b != 0) :
    (factorizationLCMLeft a b) * (factorizationLCMRight a b) = lcm a b := by
  rw [← prod_factorization_pow_eq_self (lcm_ne_zero ha hb)]; rw [factorizationLCMLeft]; rw [factorizationLCMRight]; rw [← prod_mul]
  congr; ext p n; split_ifs <;> simp

variable (a b)

/--
lemma `factorizationLCMLeft_dvd_left` / 引理 `factorizationLCMLeft_dvd_left`

English:
lemma factorizationLCMLeft_dvd_left
  statement: factorizationLCMLeft a b ∣ a
  proof: by
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [dvd_zero]
  rcases eq_or_ne b 0 with rfl | hb
  · simp [factorizationLCMLeft]
  nth_rewrite 2 [← prod_factorization_pow_eq_self ha]
  rw [prod_of_support_subset (s := (lcm a b).factorization.support)]
  · apply prod_dvd_prod_of_dvd; rintro p -; d

中文:
引理 factorizationLCMLeft_dvd_left
  结论: factorizationLCMLeft a b ∣ a
  证明: by
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [dvd_zero]
  rcases eq_or_ne b 0 with rfl | hb
  · simp [factorizationLCMLeft]
  nth_rewrite 2 [← prod_factorization_pow_eq_self ha]
  rw [prod_of_support_subset (s := (lcm a b).factorization.support)]
  · apply prod_dvd_prod_of_dvd; rintro p -; d

Depends on / 依赖: dvd_zero, eq_or_ne, factorization, factorization.support, factorizationLCMLeft, factorization_lcm, le_rfl, lt_sup_iff, lt_sup_iff.mpr, mem_support_iff, nth_rewrite, one_dvd, pow_dvd_pow, prod_dvd_prod_of_dvd, prod_factorization_pow_eq_self, prod_of_support_subset, split_ifs, sup_le, support
-/
lemma factorizationLCMLeft_dvd_left : factorizationLCMLeft a b ∣ a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [dvd_zero]
  rcases eq_or_ne b 0 with rfl | hb
  · simp [factorizationLCMLeft]
  nth_rewrite 2 [← prod_factorization_pow_eq_self ha]
  rw [prod_of_support_subset (s := (lcm a b).factorization.support)]
  · apply prod_dvd_prod_of_dvd; rintro p -; dsimp only; split_ifs with le
    · rw [factorization_lcm ha hb]; apply pow_dvd_pow; exact sup_le le_rfl le
    · apply one_dvd
  · intro p hp; rw [mem_support_iff] at hp ⊢
    rw [factorization_lcm ha hb]; exact (lt_sup_iff.mpr <| .inl <| Nat.pos_of_ne_zero hp).ne'
  · intros; rw [pow_zero]

/--
lemma `factorizationLCMRight_dvd_right` / 引理 `factorizationLCMRight_dvd_right`

English:
lemma factorizationLCMRight_dvd_right
  statement: factorizationLCMRight a b ∣ b
  proof: by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [factorizationLCMRight]
  rcases eq_or_ne b 0 with rfl | hb
  · simp only [dvd_zero]
  nth_rewrite 2 [← prod_factorization_pow_eq_self hb]
  rw [prod_of_support_subset (s := (lcm a b).factorization.support)]
  · apply Finset.prod_dvd_prod_of_dvd; rintr

中文:
引理 factorizationLCMRight_dvd_right
  结论: factorizationLCMRight a b ∣ b
  证明: by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [factorizationLCMRight]
  rcases eq_or_ne b 0 with rfl | hb
  · simp only [dvd_zero]
  nth_rewrite 2 [← prod_factorization_pow_eq_self hb]
  rw [prod_of_support_subset (s := (lcm a b).factorization.support)]
  · apply Finset.prod_dvd_prod_of_dvd; rintr

Depends on / 依赖: Finset, Finset.prod_dvd_prod_of_dvd, dvd_zero, eq_or_ne, factorization, factorization.support, factorizationLCMRight, factorization_lcm, le_rfl, mem_support_iff, not_le, nth_rewrite, one_dvd, pow_dvd_pow, prod_dvd_prod_of_dvd, prod_factorization_pow_eq_self, prod_of_support_subset, split_ifs, sup_le, support
-/
lemma factorizationLCMRight_dvd_right : factorizationLCMRight a b ∣ b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [factorizationLCMRight]
  rcases eq_or_ne b 0 with rfl | hb
  · simp only [dvd_zero]
  nth_rewrite 2 [← prod_factorization_pow_eq_self hb]
  rw [prod_of_support_subset (s := (lcm a b).factorization.support)]
  · apply Finset.prod_dvd_prod_of_dvd; rintro p -; dsimp only; split_ifs with le
    · apply one_dvd
    · rw [factorization_lcm ha hb]; apply pow_dvd_pow; exact sup_le (not_le.1 le).le le_rfl
  · intro p hp; rw [mem_support_iff] at hp ⊢
    rw [factorization_lcm ha hb]; exact (lt_sup_iff.mpr <| .inr <| Nat.pos_of_ne_zero hp).ne'
  · intros; rw [pow_zero]


end Nat
