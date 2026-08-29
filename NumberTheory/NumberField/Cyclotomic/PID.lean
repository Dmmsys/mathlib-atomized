/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

/-!
# Cyclotomic fields whose ring of integers is a PID.

We prove that `ℤ [ζₚ]` is a PID for specific values of `p`. The result holds for `p ≤ 19`,
but the proof is more and more involved.

## Main results
* `three_pid`: If `IsCyclotomicExtension {3} ℚ K` then `𝓞 K` is a principal ideal domain.
* `five_pid`: If `IsCyclotomicExtension {5} ℚ K` then `𝓞 K` is a principal ideal domain.
-/

public section

universe u

namespace IsCyclotomicExtension.Rat

open NumberField Polynomial InfinitePlace Nat Real cyclotomic

variable (K : Type u) [Field K] [NumberField K]

/--
theorem `three_pid` / 定理 `three_pid`

English:
theorem three_pid
  given: [IsCyclotomicExtension {3} Rat K]
  statement: IsPrincipalIdealRing (𝓞 K)
  proof: by
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [discr_prime 3 K]; rw [IsCyclotomicExtension.finrank (n := 3) K
    (irreducible_rat (by simp))]; rw [nrComplexPlaces_eq_totient_div_two 3]; rw [totient_prime
      Nat.prime_three]
  simp only [Int.reduceNeg, succ_sub_succ_eq_sub, tsub_zero, zero_lt_two, Nat.div_self, pow_one,
    cast_ofNat, neg_mul, one_mul, abs_neg, Int.cast_abs, Int.cast_ofNat,
    abs_of_pos (zero_lt_three' Real), factorial_two]
  suffices (2 * (3 / 4) * (2 ^ 2 / 2)) ^ 2 < (2 * (π / 4) * (2 ^ 2 / 2)) ^ 2 from
    lt_trans (by norm_num) this
  gcongr
  exact pi_gt_three

中文:
定理 three_pid
  条件: [是CyclotomicExtension {3} 有理数 K]
  结论: 是主理想环 (𝓞 K)
  证明: by
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [discr_prime 3 K]; rw [IsCyclotomicExtension.finrank (n := 3) K
    (irreducible_rat (by simp))]; rw [nrComplexPlaces_eq_totient_div_two 3]; rw [totient_prime
      Nat.prime_three]
  simp only [Int.reduceNeg, succ_sub_succ_eq_sub, tsub_zero, zero_lt_two, Nat.div_self, pow_one,
    cast_ofNat, neg_mul, one_mul, abs_neg, Int.cast_abs, Int.cast_ofNat,
    abs_of_pos (zero_lt_three' Real), factorial_two]
  suffices (2 * (3 / 4) * (2 ^ 2 / 2)) ^ 2 < (2 * (π / 4) * (2 ^ 2 / 2)) ^ 2 from
    lt_trans (by norm_num) this
  gcongr
  exact pi_gt_three

Depends on / 依赖: Int.cast_abs, Int.cast_ofNat, Int.reduceNeg, IsCyclotomicExtension, IsCyclotomicExtension.finrank, Nat.div_self, Nat.prime_three, RingOfIntegers, RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt, abs_neg, abs_of_pos, cast_abs, cast_ofNat, discr_prime, div_self, factorial_two, finrank, irreducible_rat, isPrincipalIdealRing_of_abs_discr_lt, neg_mul
-/
theorem three_pid [IsCyclotomicExtension {3} Rat K] : IsPrincipalIdealRing (𝓞 K) := by
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [discr_prime 3 K]; rw [IsCyclotomicExtension.finrank (n := 3) K
    (irreducible_rat (by simp))]; rw [nrComplexPlaces_eq_totient_div_two 3]; rw [totient_prime
      Nat.prime_three]
  simp only [Int.reduceNeg, succ_sub_succ_eq_sub, tsub_zero, zero_lt_two, Nat.div_self, pow_one,
    cast_ofNat, neg_mul, one_mul, abs_neg, Int.cast_abs, Int.cast_ofNat,
    abs_of_pos (zero_lt_three' Real), factorial_two]
  suffices (2 * (3 / 4) * (2 ^ 2 / 2)) ^ 2 < (2 * (π / 4) * (2 ^ 2 / 2)) ^ 2 from
    lt_trans (by norm_num) this
  gcongr
  exact pi_gt_three

/--
theorem `five_pid` / 定理 `five_pid`

English:
theorem five_pid
  given: [IsCyclotomicExtension {5} Rat K]
  statement: IsPrincipalIdealRing (𝓞 K)
  proof: by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [discr_prime 5 K]; rw [IsCyclotomicExtension.finrank (n := 5) K
    (irreducible_rat (by simp))]; rw [nrComplexPlaces_eq_totient_div_two 5]; rw [totient_prime Nat.prime_five]
  simp only [Int.reduceNeg, succ_sub_succ_eq_sub, tsub_zero, reduceDiv, even_two, Even.neg_pow,
    one_pow, cast_ofNat, Int.reducePow, one_mul, Int.cast_abs, Int.cast_ofNat,
    abs_of_pos (show (0 : Real) < 125 by simp), div_pow, show 4! = 24 by rfl]
  suffices (2 * (3 ^ 2 / 4 ^ 2) * (4 ^ 4 / 24)) ^ 2 < (2 * (π ^ 2 / 4 ^ 2) * (4 ^ 4 / 24)) ^ 2 from
    lt_trans (by norm_num) this
  gcongr
  exact pi_gt_three

中文:
定理 five_pid
  条件: [是CyclotomicExtension {5} 有理数 K]
  结论: 是主理想环 (𝓞 K)
  证明: by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [discr_prime 5 K]; rw [IsCyclotomicExtension.finrank (n := 5) K
    (irreducible_rat (by simp))]; rw [nrComplexPlaces_eq_totient_div_two 5]; rw [totient_prime Nat.prime_five]
  simp only [Int.reduceNeg, succ_sub_succ_eq_sub, tsub_zero, reduceDiv, even_two, Even.neg_pow,
    one_pow, cast_ofNat, Int.reducePow, one_mul, Int.cast_abs, Int.cast_ofNat,
    abs_of_pos (show (0 : Real) < 125 by simp), div_pow, show 4! = 24 by rfl]
  suffices (2 * (3 ^ 2 / 4 ^ 2) * (4 ^ 4 / 24)) ^ 2 < (2 * (π ^ 2 / 4 ^ 2) * (4 ^ 4 / 24)) ^ 2 from
    lt_trans (by norm_num) this
  gcongr
  exact pi_gt_three

Depends on / 依赖: Even.neg_pow, Int.cast_abs, Int.cast_ofNat, Int.reduceNeg, Int.reducePow, IsCyclotomicExtension, IsCyclotomicExtension.finrank, Nat.Prime, Nat.prime_five, RingOfIntegers, RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt, abs_of_pos, cast_abs, cast_ofNat, discr_prime, div_po, even_two, finrank, irreducible_rat, isPrincipalIdealRing_of_abs_discr_lt
-/
theorem five_pid [IsCyclotomicExtension {5} Rat K] : IsPrincipalIdealRing (𝓞 K) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [discr_prime 5 K]; rw [IsCyclotomicExtension.finrank (n := 5) K
    (irreducible_rat (by simp))]; rw [nrComplexPlaces_eq_totient_div_two 5]; rw [totient_prime Nat.prime_five]
  simp only [Int.reduceNeg, succ_sub_succ_eq_sub, tsub_zero, reduceDiv, even_two, Even.neg_pow,
    one_pow, cast_ofNat, Int.reducePow, one_mul, Int.cast_abs, Int.cast_ofNat,
    abs_of_pos (show (0 : Real) < 125 by simp), div_pow, show 4! = 24 by rfl]
  suffices (2 * (3 ^ 2 / 4 ^ 2) * (4 ^ 4 / 24)) ^ 2 < (2 * (π ^ 2 / 4 ^ 2) * (4 ^ 4 / 24)) ^ 2 from
    lt_trans (by norm_num) this
  gcongr
  exact pi_gt_three

end IsCyclotomicExtension.Rat
