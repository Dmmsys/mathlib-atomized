/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Special values of Hurwitz and Riemann zeta functions

This file gives the formula for `ζ (2 * k)`, for `k` a non-zero integer, in terms of Bernoulli
numbers. More generally, we give formulae for any Hurwitz zeta functions at any (strictly) negative
integer in terms of Bernoulli polynomials.

(Note that most of the actual work for these formulae is done elsewhere, in
`Mathlib/NumberTheory/ZetaValues.lean`. This file has only those results which really need the
definition of Hurwitz zeta and related functions, rather than working directly with the defining
sums in the convergence range.)

## Main results

- `hurwitzZeta_neg_nat`: for `k : ℕ` with `k ≠ 0`, and any `x ∈ ℝ / ℤ`, the special value
  `hurwitzZeta x (-k)` is equal to `-(Polynomial.bernoulli (k + 1) x) / (k + 1)`.
- `riemannZeta_neg_nat_eq_bernoulli` : for any `k ∈ ℕ` we have the formula
  `riemannZeta (-k) = (-1) ^ k * bernoulli (k + 1) / (k + 1)`
- `riemannZeta_two_mul_nat`: formula for `ζ(2 * k)` for `k ∈ ℕ, k ≠ 0` in terms of Bernoulli
  numbers

## TODO

* Extend to cover Dirichlet L-functions.
* The formulae are correct for `s = 0` as well, but we do not prove this case, since this requires
  Fourier series which are only conditionally convergent, which is difficult to approach using the
  methods in the library at the present time (May 2024).
-/

public section

open Complex Real Set

open scoped Nat

namespace HurwitzZeta

variable {k : Nat} {x : Real}

/--
theorem `cosZeta_two_mul_nat` / 定理 `cosZeta_two_mul_nat`

English:
theorem cosZeta_two_mul_nat
  given: (hk : k != 0) (hx : x in Icc 0 1)
  proof: by
  rw [← (hasSum_nat_cosZeta x (?_ : 1 < re (2 * k))).tsum_eq]
· refine Eq.trans ?_
      (congr_arg ofReal (hasSum_one_div_nat_pow_mul_cos hk hx).tsum_eq).trans ?_
    · rw [ofReal_tsum]
      refine tsum_congr fun n => ?_
      norm_cast
      ring_nf
    · push_cast
      congr 1
      have : (Polynomial.bernoulli (2 * k)).map (algebraMap Rat Complex) = _ :=
        (Polynomial.map_map (algebraMap Rat Real) ofRealHom _).symm
      rw [this]; rw [← ofRealHom_eq_coe]; rw [← ofRealHom_eq_coe]
      apply Polynomial.map_aeval_eq_aeval_map (by simp)
  · norm_cast
    lia

中文:
定理 cosZeta_two_mul_nat
  条件: (hk : k != 0) (hx : x in 闭区间 0 1)
  证明: by
  rw [← (hasSum_nat_cosZeta x (?_ : 1 < re (2 * k))).tsum_eq]
· refine Eq.trans ?_
      (congr_arg ofReal (hasSum_one_div_nat_pow_mul_cos hk hx).tsum_eq).trans ?_
    · rw [ofReal_tsum]
      refine tsum_congr fun n => ?_
      norm_cast
      ring_nf
    · push_cast
      congr 1
      have : (Polynomial.bernoulli (2 * k)).map (algebraMap Rat Complex) = _ :=
        (Polynomial.map_map (algebraMap Rat Real) ofRealHom _).symm
      rw [this]; rw [← ofRealHom_eq_coe]; rw [← ofRealHom_eq_coe]
      apply Polynomial.map_aeval_eq_aeval_map (by simp)
  · norm_cast
    lia

Depends on / 依赖: Eq.trans, Polynomial, Polynomial.bernoulli, Polynomial.map_aeval_eq_aeval_map, Polynomial.map_map, algebraMap, bernoulli, congr_arg, hasSum_nat_cosZeta, hasSum_one_div_nat_pow_mul_cos, map_aeval_eq_aeval_map, map_map, norm_cas, ofReal, ofRealHom, ofRealHom_eq_coe, ofReal_tsum, ring_nf, tsum_congr, tsum_eq
-/
theorem cosZeta_two_mul_nat (hk : k != 0) (hx : x in Icc 0 1) :
    cosZeta x (2 * k) = (-1) ^ (k + 1) * (2 * π) ^ (2 * k) / 2 / (2 * k)! *
      ((Polynomial.bernoulli (2 * k)).map (algebraMap Rat Complex)).eval (x : Complex) := by
  rw [← (hasSum_nat_cosZeta x (?_ : 1 < re (2 * k))).tsum_eq]
· refine Eq.trans ?_
      (congr_arg ofReal (hasSum_one_div_nat_pow_mul_cos hk hx).tsum_eq).trans ?_
    · rw [ofReal_tsum]
      refine tsum_congr fun n => ?_
      norm_cast
      ring_nf
    · push_cast
      congr 1
      have : (Polynomial.bernoulli (2 * k)).map (algebraMap Rat Complex) = _ :=
        (Polynomial.map_map (algebraMap Rat Real) ofRealHom _).symm
      rw [this]; rw [← ofRealHom_eq_coe]; rw [← ofRealHom_eq_coe]
      apply Polynomial.map_aeval_eq_aeval_map (by simp)
  · norm_cast
    lia

/--
theorem `sinZeta_two_mul_nat_add_one` / 定理 `sinZeta_two_mul_nat_add_one`

English:
theorem sinZeta_two_mul_nat_add_one
  given: (hk : k != 0) (hx : x in Icc 0 1)
  proof: by
  rw [← (hasSum_nat_sinZeta x (?_ : 1 < re (2 * k + 1))).tsum_eq]
· refine Eq.trans ?_
      (congr_arg ofReal (hasSum_one_div_nat_pow_mul_sin hk hx).tsum_eq).trans ?_
    · rw [ofReal_tsum]
      refine tsum_congr fun n => ?_
      norm_cast
      ring_nf
    · push_cast
      congr 1
      have : (Polynomial.bernoulli (2 * k + 1)).map (algebraMap Rat Complex) = _ :=
        (Polynomial.map_map (algebraMap Rat Real) ofRealHom _).symm
      rw [this]; rw [← ofRealHom_eq_coe]; rw [← ofRealHom_eq_coe]
      apply Polynomial.map_aeval_eq_aeval_map (by simp)
  · norm_cast
    lia

中文:
定理 sinZeta_two_mul_nat_add_one
  条件: (hk : k != 0) (hx : x in 闭区间 0 1)
  证明: by
  rw [← (hasSum_nat_sinZeta x (?_ : 1 < re (2 * k + 1))).tsum_eq]
· refine Eq.trans ?_
      (congr_arg ofReal (hasSum_one_div_nat_pow_mul_sin hk hx).tsum_eq).trans ?_
    · rw [ofReal_tsum]
      refine tsum_congr fun n => ?_
      norm_cast
      ring_nf
    · push_cast
      congr 1
      have : (Polynomial.bernoulli (2 * k + 1)).map (algebraMap Rat Complex) = _ :=
        (Polynomial.map_map (algebraMap Rat Real) ofRealHom _).symm
      rw [this]; rw [← ofRealHom_eq_coe]; rw [← ofRealHom_eq_coe]
      apply Polynomial.map_aeval_eq_aeval_map (by simp)
  · norm_cast
    lia

Depends on / 依赖: Eq.trans, Polynomial, Polynomial.bernoulli, Polynomial.map_aeval_eq_aeval_map, Polynomial.map_map, algebraMap, bernoulli, congr_arg, hasSum_nat_sinZeta, hasSum_one_div_nat_pow_mul_sin, map_aeval_eq_aeval_map, map_map, ofReal, ofRealHom, ofRealHom_eq_coe, ofReal_tsum, ring_nf, tsum_congr, tsum_eq
-/
theorem sinZeta_two_mul_nat_add_one (hk : k != 0) (hx : x in Icc 0 1) :
    sinZeta x (2 * k + 1) = (-1) ^ (k + 1) * (2 * π) ^ (2 * k + 1) / 2 / (2 * k + 1)! *
      ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap Rat Complex)).eval (x : Complex) := by
  rw [← (hasSum_nat_sinZeta x (?_ : 1 < re (2 * k + 1))).tsum_eq]
· refine Eq.trans ?_
      (congr_arg ofReal (hasSum_one_div_nat_pow_mul_sin hk hx).tsum_eq).trans ?_
    · rw [ofReal_tsum]
      refine tsum_congr fun n => ?_
      norm_cast
      ring_nf
    · push_cast
      congr 1
      have : (Polynomial.bernoulli (2 * k + 1)).map (algebraMap Rat Complex) = _ :=
        (Polynomial.map_map (algebraMap Rat Real) ofRealHom _).symm
      rw [this]; rw [← ofRealHom_eq_coe]; rw [← ofRealHom_eq_coe]
      apply Polynomial.map_aeval_eq_aeval_map (by simp)
  · norm_cast
    lia

/--
theorem `cosZeta_two_mul_nat'` / 定理 `cosZeta_two_mul_nat'`

English:
theorem cosZeta_two_mul_nat'
  given: (hk : k != 0) (hx : x in Icc (0 : Real) 1)
  proof: by
  rw [cosZeta_two_mul_nat hk hx]
  congr 1
  have : (2 * k)! = (2 * k) * Complex.Gamma (2 * k) := by
    rw [(by { norm_cast; lia } : 2 * (k : Complex) = ↑(2 * k - 1) + 1)]; rw [Complex.Gamma_nat_eq_factorial]; rw [← Nat.cast_add_one]; rw [← Nat.cast_mul]; rw [← Nat.factorial_succ]; rw [Nat.sub_add_cancel (by lia)]
  simp_rw [this, GammaComplex, cpow_neg, ← div_div, div_inv_eq_mul, div_mul_eq_mul_div, div_div,
    mul_right_comm (2 : Complex) (k : Complex)]
  norm_cast

中文:
定理 cosZeta_two_mul_nat'
  条件: (hk : k != 0) (hx : x in 闭区间 (0 : 实数) 1)
  证明: by
  rw [cosZeta_two_mul_nat hk hx]
  congr 1
  have : (2 * k)! = (2 * k) * Complex.Gamma (2 * k) := by
    rw [(by { norm_cast; lia } : 2 * (k : Complex) = ↑(2 * k - 1) + 1)]; rw [Complex.Gamma_nat_eq_factorial]; rw [← Nat.cast_add_one]; rw [← Nat.cast_mul]; rw [← Nat.factorial_succ]; rw [Nat.sub_add_cancel (by lia)]
  simp_rw [this, GammaComplex, cpow_neg, ← div_div, div_inv_eq_mul, div_mul_eq_mul_div, div_div,
    mul_right_comm (2 : Complex) (k : Complex)]
  norm_cast

Depends on / 依赖: Complex.Gamma, Complex.Gamma_nat_eq_factorial, GammaComplex, Gamma_nat_eq_factorial, Nat.cast_add_one, Nat.cast_mul, Nat.factorial_succ, Nat.sub_add_cancel, cast_add_one, cast_mul, cosZeta_two_mul_nat, cpow_neg, div_div, div_inv_eq_mul, div_mul_eq_mul_div, factorial_succ, mul_right_comm, simp_rw, sub_add_cancel
-/
theorem cosZeta_two_mul_nat' (hk : k != 0) (hx : x in Icc (0 : Real) 1) :
    cosZeta x (2 * k) = (-1) ^ (k + 1) / (2 * k) / GammaComplex (2 * k) *
      ((Polynomial.bernoulli (2 * k)).map (algebraMap Rat Complex)).eval (x : Complex) := by
  rw [cosZeta_two_mul_nat hk hx]
  congr 1
  have : (2 * k)! = (2 * k) * Complex.Gamma (2 * k) := by
    rw [(by { norm_cast; lia } : 2 * (k : Complex) = ↑(2 * k - 1) + 1)]; rw [Complex.Gamma_nat_eq_factorial]; rw [← Nat.cast_add_one]; rw [← Nat.cast_mul]; rw [← Nat.factorial_succ]; rw [Nat.sub_add_cancel (by lia)]
  simp_rw [this, GammaComplex, cpow_neg, ← div_div, div_inv_eq_mul, div_mul_eq_mul_div, div_div,
    mul_right_comm (2 : Complex) (k : Complex)]
  norm_cast

/--
theorem `sinZeta_two_mul_nat_add_one'` / 定理 `sinZeta_two_mul_nat_add_one'`

English:
theorem sinZeta_two_mul_nat_add_one'
  given: (hk : k != 0) (hx : x in Icc (0 : Real) 1)
  proof: by
  rw [sinZeta_two_mul_nat_add_one hk hx]
  congr 1
  have : (2 * k + 1)! = (2 * k + 1) * Complex.Gamma (2 * k + 1) := by
    rw [(by simp : Complex.Gamma (2 * k + 1) = Complex.Gamma (↑(2 * k) + 1))]; rw [Complex.Gamma_nat_eq_factorial]; rw [← Nat.cast_ofNat (R := Complex)]; rw [← Nat.cast_mul]; rw [← Nat.cast_add_one]; rw [← Nat.cast_mul]; rw [← Nat.factorial_succ]
  simp_rw [this, GammaComplex, cpow_neg, ← div_div, div_inv_eq_mul, div_mul_eq_mul_div, div_div]
  rw [(by simp : 2 * (k : Complex) + 1 = ↑(2 * k + 1))]; rw [cpow_natCast]
  ring

中文:
定理 sinZeta_two_mul_nat_add_one'
  条件: (hk : k != 0) (hx : x in 闭区间 (0 : 实数) 1)
  证明: by
  rw [sinZeta_two_mul_nat_add_one hk hx]
  congr 1
  have : (2 * k + 1)! = (2 * k + 1) * Complex.Gamma (2 * k + 1) := by
    rw [(by simp : Complex.Gamma (2 * k + 1) = Complex.Gamma (↑(2 * k) + 1))]; rw [Complex.Gamma_nat_eq_factorial]; rw [← Nat.cast_ofNat (R := Complex)]; rw [← Nat.cast_mul]; rw [← Nat.cast_add_one]; rw [← Nat.cast_mul]; rw [← Nat.factorial_succ]
  simp_rw [this, GammaComplex, cpow_neg, ← div_div, div_inv_eq_mul, div_mul_eq_mul_div, div_div]
  rw [(by simp : 2 * (k : Complex) + 1 = ↑(2 * k + 1))]; rw [cpow_natCast]
  ring

Depends on / 依赖: Complex.Gamma, Complex.Gamma_nat_eq_factorial, GammaComplex, Gamma_nat_eq_factorial, Nat.cast_add_one, Nat.cast_mul, Nat.cast_ofNat, Nat.factorial_succ, cast_add_one, cast_mul, cast_ofNat, cpow_neg, div_div, div_inv_eq_mul, div_mul_eq_mul_div, factorial_succ, simp_rw, sinZeta_two_mul_nat_add_one
-/
theorem sinZeta_two_mul_nat_add_one' (hk : k != 0) (hx : x in Icc (0 : Real) 1) :
    sinZeta x (2 * k + 1) = (-1) ^ (k + 1) / (2 * k + 1) / GammaComplex (2 * k + 1) *
      ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap Rat Complex)).eval (x : Complex) := by
  rw [sinZeta_two_mul_nat_add_one hk hx]
  congr 1
  have : (2 * k + 1)! = (2 * k + 1) * Complex.Gamma (2 * k + 1) := by
    rw [(by simp : Complex.Gamma (2 * k + 1) = Complex.Gamma (↑(2 * k) + 1))]; rw [Complex.Gamma_nat_eq_factorial]; rw [← Nat.cast_ofNat (R := Complex)]; rw [← Nat.cast_mul]; rw [← Nat.cast_add_one]; rw [← Nat.cast_mul]; rw [← Nat.factorial_succ]
  simp_rw [this, GammaComplex, cpow_neg, ← div_div, div_inv_eq_mul, div_mul_eq_mul_div, div_div]
  rw [(by simp : 2 * (k : Complex) + 1 = ↑(2 * k + 1))]; rw [cpow_natCast]
  ring

/--
theorem `hurwitzZetaEven_one_sub_two_mul_nat` / 定理 `hurwitzZetaEven_one_sub_two_mul_nat`

English:
theorem hurwitzZetaEven_one_sub_two_mul_nat
  given: (hk : k != 0) (hx : x in Icc (0 : Real) 1)
  proof: by
  have h1 (n : Nat) : (2 * k : Complex) != -n := by
    rw [← Int.cast_ofNat]; rw [← Int.cast_natCast]; rw [← Int.cast_mul]; rw [← Int.cast_natCast n]; rw [← Int.cast_neg]; rw [Ne]; rw [Int.cast_inj]; rw [← Ne]
    refine ne_of_gt ((neg_nonpos_of_nonneg n.cast_nonneg).trans_lt (mul_pos two_pos ?_))
    exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have h2 : (2 * k : Complex) != 1 := by norm_cast; simp
  have h3 : GammaComplex (2 * k) != 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero h1)
    simp [pi_ne_zero]
  rw [hurwitzZetaEven_one_sub _ h1 (Or.inr h2)]; rw [← GammaComplex]; rw [cosZeta_two_mul_nat' hk hx]; rw [← mul_assoc]; rw [← mul_div_assoc]; rw [mul_assoc]; rw [mul_div_cancel_left₀ _ h3]; rw [← mul_div_assoc]
  congr 2
  rw [mul_div_assoc]; rw [mul_div_cancel_left₀ _ two_ne_zero]; rw [← ofReal_natCast]; rw [← ofReal_mul]; rw [← ofReal_cos]; rw [mul_comm π]; rw [← sub_zero (k * π)]; rw [cos_nat_mul_pi_sub]; rw [Real.cos_zero]; rw [mul_one]; rw [ofReal_pow]; rw [ofReal_neg]; rw [ofReal_one]; rw [pow_succ]; rw [mul_neg_one]; rw [mul_neg]; rw [← mul_pow]; rw [neg_one_mul]; rw [neg_neg]; rw [one_pow]

中文:
定理 hurwitzZetaEven_one_sub_two_mul_nat
  条件: (hk : k != 0) (hx : x in 闭区间 (0 : 实数) 1)
  证明: by
  have h1 (n : Nat) : (2 * k : Complex) != -n := by
    rw [← Int.cast_ofNat]; rw [← Int.cast_natCast]; rw [← Int.cast_mul]; rw [← Int.cast_natCast n]; rw [← Int.cast_neg]; rw [Ne]; rw [Int.cast_inj]; rw [← Ne]
    refine ne_of_gt ((neg_nonpos_of_nonneg n.cast_nonneg).trans_lt (mul_pos two_pos ?_))
    exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have h2 : (2 * k : Complex) != 1 := by norm_cast; simp
  have h3 : GammaComplex (2 * k) != 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero h1)
    simp [pi_ne_zero]
  rw [hurwitzZetaEven_one_sub _ h1 (Or.inr h2)]; rw [← GammaComplex]; rw [cosZeta_two_mul_nat' hk hx]; rw [← mul_assoc]; rw [← mul_div_assoc]; rw [mul_assoc]; rw [mul_div_cancel_left₀ _ h3]; rw [← mul_div_assoc]
  congr 2
  rw [mul_div_assoc]; rw [mul_div_cancel_left₀ _ two_ne_zero]; rw [← ofReal_natCast]; rw [← ofReal_mul]; rw [← ofReal_cos]; rw [mul_comm π]; rw [← sub_zero (k * π)]; rw [cos_nat_mul_pi_sub]; rw [Real.cos_zero]; rw [mul_one]; rw [ofReal_pow]; rw [ofReal_neg]; rw [ofReal_one]; rw [pow_succ]; rw [mul_neg_one]; rw [mul_neg]; rw [← mul_pow]; rw [neg_one_mul]; rw [neg_neg]; rw [one_pow]

Depends on / 依赖: GammaComplex, Gamma_ne_zero, Int.cast_inj, Int.cast_mul, Int.cast_natCast, Int.cast_neg, Int.cast_ofNat, Nat.cast_pos.mpr, Nat.pos_of_ne_zero, cast_inj, cast_mul, cast_natCast, cast_neg, cast_nonneg, cast_ofNat, cast_pos, mul_ne_zero, mul_pos, n.cast_nonneg, ne_of_gt
-/
theorem hurwitzZetaEven_one_sub_two_mul_nat (hk : k != 0) (hx : x in Icc (0 : Real) 1) :
    hurwitzZetaEven x (1 - 2 * k) =
      -1 / (2 * k) * ((Polynomial.bernoulli (2 * k)).map (algebraMap Rat Complex)).eval (x : Complex) := by
  have h1 (n : Nat) : (2 * k : Complex) != -n := by
    rw [← Int.cast_ofNat]; rw [← Int.cast_natCast]; rw [← Int.cast_mul]; rw [← Int.cast_natCast n]; rw [← Int.cast_neg]; rw [Ne]; rw [Int.cast_inj]; rw [← Ne]
    refine ne_of_gt ((neg_nonpos_of_nonneg n.cast_nonneg).trans_lt (mul_pos two_pos ?_))
    exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have h2 : (2 * k : Complex) != 1 := by norm_cast; simp
  have h3 : GammaComplex (2 * k) != 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero h1)
    simp [pi_ne_zero]
  rw [hurwitzZetaEven_one_sub _ h1 (Or.inr h2)]; rw [← GammaComplex]; rw [cosZeta_two_mul_nat' hk hx]; rw [← mul_assoc]; rw [← mul_div_assoc]; rw [mul_assoc]; rw [mul_div_cancel_left₀ _ h3]; rw [← mul_div_assoc]
  congr 2
  rw [mul_div_assoc]; rw [mul_div_cancel_left₀ _ two_ne_zero]; rw [← ofReal_natCast]; rw [← ofReal_mul]; rw [← ofReal_cos]; rw [mul_comm π]; rw [← sub_zero (k * π)]; rw [cos_nat_mul_pi_sub]; rw [Real.cos_zero]; rw [mul_one]; rw [ofReal_pow]; rw [ofReal_neg]; rw [ofReal_one]; rw [pow_succ]; rw [mul_neg_one]; rw [mul_neg]; rw [← mul_pow]; rw [neg_one_mul]; rw [neg_neg]; rw [one_pow]

/--
theorem `hurwitzZetaOdd_neg_two_mul_nat` / 定理 `hurwitzZetaOdd_neg_two_mul_nat`

English:
theorem hurwitzZetaOdd_neg_two_mul_nat
  given: (hk : k != 0) (hx : x in Icc (0 : Real) 1)
  proof: by
  have h1 (n : Nat) : (2 * k + 1 : Complex) != -n := by
    rw [← Int.cast_ofNat]; rw [← Int.cast_natCast]; rw [← Int.cast_mul]; rw [← Int.cast_natCast n]; rw [← Int.cast_neg]; rw [← Int.cast_one]; rw [← Int.cast_add]; rw [Ne]; rw [Int.cast_inj]; rw [← Ne]
    refine ne_of_gt ((neg_nonpos_of_nonneg n.cast_nonneg).trans_lt ?_)
    positivity
  have h3 : GammaComplex (2 * k + 1) != 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero h1)
    simp [pi_ne_zero]
  rw [(by simp : -(2 * k : Complex) = 1 - (2 * k + 1))]; rw [hurwitzZetaOdd_one_sub _ h1]; rw [← GammaComplex]; rw [sinZeta_two_mul_nat_add_one' hk hx]; rw [← mul_assoc]; rw [← mul_div_assoc]; rw [mul_assoc]; rw [mul_div_cancel_left₀ _ h3]; rw [← mul_div_assoc]
  congr 2
  rw [mul_div_assoc]; rw [add_div]; rw [mul_div_cancel_left₀ _ two_ne_zero]; rw [← ofReal_natCast]; rw [← ofReal_one]; rw [← ofReal_ofNat]; rw [← ofReal_div]; rw [← ofReal_add]; rw [← ofReal_mul]; rw [← ofReal_sin]; rw [mul_comm π]; rw [add_mul]; rw [mul_comm (1 / 2)]; rw [mul_one_div]; rw [Real.sin_add_pi_div_two]; rw [← sub_zero (k * π)]; rw [cos_nat_mul_pi_sub]; rw [Real.cos_zero]; rw [mul_one]; rw [ofReal_pow]; rw [ofReal_neg]; rw [ofReal_one]; rw [pow_succ]; rw [mul_neg_one]; rw [mul_neg]; rw [← mul_pow]; rw [neg_one_mul]; rw [neg_neg]; rw [one_pow]

中文:
定理 hurwitzZetaOdd_neg_two_mul_nat
  条件: (hk : k != 0) (hx : x in 闭区间 (0 : 实数) 1)
  证明: by
  have h1 (n : Nat) : (2 * k + 1 : Complex) != -n := by
    rw [← Int.cast_ofNat]; rw [← Int.cast_natCast]; rw [← Int.cast_mul]; rw [← Int.cast_natCast n]; rw [← Int.cast_neg]; rw [← Int.cast_one]; rw [← Int.cast_add]; rw [Ne]; rw [Int.cast_inj]; rw [← Ne]
    refine ne_of_gt ((neg_nonpos_of_nonneg n.cast_nonneg).trans_lt ?_)
    positivity
  have h3 : GammaComplex (2 * k + 1) != 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero h1)
    simp [pi_ne_zero]
  rw [(by simp : -(2 * k : Complex) = 1 - (2 * k + 1))]; rw [hurwitzZetaOdd_one_sub _ h1]; rw [← GammaComplex]; rw [sinZeta_two_mul_nat_add_one' hk hx]; rw [← mul_assoc]; rw [← mul_div_assoc]; rw [mul_assoc]; rw [mul_div_cancel_left₀ _ h3]; rw [← mul_div_assoc]
  congr 2
  rw [mul_div_assoc]; rw [add_div]; rw [mul_div_cancel_left₀ _ two_ne_zero]; rw [← ofReal_natCast]; rw [← ofReal_one]; rw [← ofReal_ofNat]; rw [← ofReal_div]; rw [← ofReal_add]; rw [← ofReal_mul]; rw [← ofReal_sin]; rw [mul_comm π]; rw [add_mul]; rw [mul_comm (1 / 2)]; rw [mul_one_div]; rw [Real.sin_add_pi_div_two]; rw [← sub_zero (k * π)]; rw [cos_nat_mul_pi_sub]; rw [Real.cos_zero]; rw [mul_one]; rw [ofReal_pow]; rw [ofReal_neg]; rw [ofReal_one]; rw [pow_succ]; rw [mul_neg_one]; rw [mul_neg]; rw [← mul_pow]; rw [neg_one_mul]; rw [neg_neg]; rw [one_pow]

Depends on / 依赖: GammaComplex, Gamma_ne_zero, Int.cast_add, Int.cast_inj, Int.cast_mul, Int.cast_natCast, Int.cast_neg, Int.cast_ofNat, Int.cast_one, cast_add, cast_inj, cast_mul, cast_natCast, cast_neg, cast_nonneg, cast_ofNat, cast_one, mul_ne_zero, n.cast_nonneg, ne_of_gt
-/
theorem hurwitzZetaOdd_neg_two_mul_nat (hk : k != 0) (hx : x in Icc (0 : Real) 1) :
    hurwitzZetaOdd x (-(2 * k)) =
    -1 / (2 * k + 1) * ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap Rat Complex)).eval (x : Complex) := by
  have h1 (n : Nat) : (2 * k + 1 : Complex) != -n := by
    rw [← Int.cast_ofNat]; rw [← Int.cast_natCast]; rw [← Int.cast_mul]; rw [← Int.cast_natCast n]; rw [← Int.cast_neg]; rw [← Int.cast_one]; rw [← Int.cast_add]; rw [Ne]; rw [Int.cast_inj]; rw [← Ne]
    refine ne_of_gt ((neg_nonpos_of_nonneg n.cast_nonneg).trans_lt ?_)
    positivity
  have h3 : GammaComplex (2 * k + 1) != 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero h1)
    simp [pi_ne_zero]
  rw [(by simp : -(2 * k : Complex) = 1 - (2 * k + 1))]; rw [hurwitzZetaOdd_one_sub _ h1]; rw [← GammaComplex]; rw [sinZeta_two_mul_nat_add_one' hk hx]; rw [← mul_assoc]; rw [← mul_div_assoc]; rw [mul_assoc]; rw [mul_div_cancel_left₀ _ h3]; rw [← mul_div_assoc]
  congr 2
  rw [mul_div_assoc]; rw [add_div]; rw [mul_div_cancel_left₀ _ two_ne_zero]; rw [← ofReal_natCast]; rw [← ofReal_one]; rw [← ofReal_ofNat]; rw [← ofReal_div]; rw [← ofReal_add]; rw [← ofReal_mul]; rw [← ofReal_sin]; rw [mul_comm π]; rw [add_mul]; rw [mul_comm (1 / 2)]; rw [mul_one_div]; rw [Real.sin_add_pi_div_two]; rw [← sub_zero (k * π)]; rw [cos_nat_mul_pi_sub]; rw [Real.cos_zero]; rw [mul_one]; rw [ofReal_pow]; rw [ofReal_neg]; rw [ofReal_one]; rw [pow_succ]; rw [mul_neg_one]; rw [mul_neg]; rw [← mul_pow]; rw [neg_one_mul]; rw [neg_neg]; rw [one_pow]

-- private because it is superseded by `hurwitzZeta_neg_nat` below
/--
lemma `hurwitzZeta_one_sub_two_mul_nat` / 引理 `hurwitzZeta_one_sub_two_mul_nat`

English:
lemma hurwitzZeta_one_sub_two_mul_nat
  given: (hk : k != 0) (hx : x in Icc (0 : Real) 1)
  proof: by
  suffices hurwitzZetaOdd x (1 - 2 * k) = 0 by
    rw [hurwitzZeta]; rw [this]; rw [add_zero]; rw [hurwitzZetaEven_one_sub_two_mul_nat hk hx]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [Nat.cast_succ]; rw [show (1 : Complex) - 2 * (k + 1) = -2 * k - 1 by ring]; rw [hurwitzZetaOdd_neg_two_mul_nat_sub_one]

中文:
引理 hurwitzZeta_one_sub_two_mul_nat
  条件: (hk : k != 0) (hx : x in 闭区间 (0 : 实数) 1)
  证明: by
  suffices hurwitzZetaOdd x (1 - 2 * k) = 0 by
    rw [hurwitzZeta]; rw [this]; rw [add_zero]; rw [hurwitzZetaEven_one_sub_two_mul_nat hk hx]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [Nat.cast_succ]; rw [show (1 : Complex) - 2 * (k + 1) = -2 * k - 1 by ring]; rw [hurwitzZetaOdd_neg_two_mul_nat_sub_one]
-/
private lemma hurwitzZeta_one_sub_two_mul_nat (hk : k != 0) (hx : x in Icc (0 : Real) 1) :
    hurwitzZeta x (1 - 2 * k) =
      -1 / (2 * k) * ((Polynomial.bernoulli (2 * k)).map (algebraMap Rat Complex)).eval (x : Complex) := by
  suffices hurwitzZetaOdd x (1 - 2 * k) = 0 by
    rw [hurwitzZeta]; rw [this]; rw [add_zero]; rw [hurwitzZetaEven_one_sub_two_mul_nat hk hx]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [Nat.cast_succ]; rw [show (1 : Complex) - 2 * (k + 1) = -2 * k - 1 by ring]; rw [hurwitzZetaOdd_neg_two_mul_nat_sub_one]

-- private because it is superseded by `hurwitzZeta_neg_nat` below
/--
lemma `hurwitzZeta_neg_two_mul_nat` / 引理 `hurwitzZeta_neg_two_mul_nat`

English:
lemma hurwitzZeta_neg_two_mul_nat
  given: (hk : k != 0) (hx : x in Icc (0 : Real) 1)
  proof: by
  suffices hurwitzZetaEven x (-(2 * k)) = 0 by
    rw [hurwitzZeta]; rw [this]; rw [zero_add]; rw [hurwitzZetaOdd_neg_two_mul_nat hk hx]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simpa using hurwitzZetaEven_neg_two_mul_nat_add_one x k

中文:
引理 hurwitzZeta_neg_two_mul_nat
  条件: (hk : k != 0) (hx : x in 闭区间 (0 : 实数) 1)
  证明: by
  suffices hurwitzZetaEven x (-(2 * k)) = 0 by
    rw [hurwitzZeta]; rw [this]; rw [zero_add]; rw [hurwitzZetaOdd_neg_two_mul_nat hk hx]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simpa using hurwitzZetaEven_neg_two_mul_nat_add_one x k
-/
private lemma hurwitzZeta_neg_two_mul_nat (hk : k != 0) (hx : x in Icc (0 : Real) 1) :
    hurwitzZeta x (-(2 * k)) = -1 / (2 * k + 1) *
      ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap Rat Complex)).eval (x : Complex) := by
  suffices hurwitzZetaEven x (-(2 * k)) = 0 by
    rw [hurwitzZeta]; rw [this]; rw [zero_add]; rw [hurwitzZetaOdd_neg_two_mul_nat hk hx]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simpa using hurwitzZetaEven_neg_two_mul_nat_add_one x k

/--
theorem `hurwitzZeta_neg_nat` / 定理 `hurwitzZeta_neg_nat`

English:
theorem hurwitzZeta_neg_nat
  given: (hk : k != 0) (hx : x in Icc (0 : Real) 1)
  proof: by
  rcases Nat.even_or_odd' k with ⟨n, (rfl | rfl)⟩
  · exact_mod_cast hurwitzZeta_neg_two_mul_nat (by lia : n != 0) hx
  · exact_mod_cast hurwitzZeta_one_sub_two_mul_nat (by lia : n + 1 != 0) hx

中文:
定理 hurwitzZeta_neg_nat
  条件: (hk : k != 0) (hx : x in 闭区间 (0 : 实数) 1)
  证明: by
  rcases Nat.even_or_odd' k with ⟨n, (rfl | rfl)⟩
  · exact_mod_cast hurwitzZeta_neg_two_mul_nat (by lia : n != 0) hx
  · exact_mod_cast hurwitzZeta_one_sub_two_mul_nat (by lia : n + 1 != 0) hx

Depends on / 依赖: Nat.even_or_odd, even_or_odd, hurwitzZeta_neg_two_mul_nat, hurwitzZeta_one_sub_two_mul_nat
-/
theorem hurwitzZeta_neg_nat (hk : k != 0) (hx : x in Icc (0 : Real) 1) :
    hurwitzZeta x (-k) =
    -1 / (k + 1) * ((Polynomial.bernoulli (k + 1)).map (algebraMap Rat Complex)).eval (x : Complex) := by
  rcases Nat.even_or_odd' k with ⟨n, (rfl | rfl)⟩
  · exact_mod_cast hurwitzZeta_neg_two_mul_nat (by lia : n != 0) hx
  · exact_mod_cast hurwitzZeta_one_sub_two_mul_nat (by lia : n + 1 != 0) hx

end HurwitzZeta

open HurwitzZeta

/--
theorem `riemannZeta_two_mul_nat` / 定理 `riemannZeta_two_mul_nat`

English:
theorem riemannZeta_two_mul_nat
  given: {k : Nat} (hk : k != 0)
  proof: by
  convert! congr_arg ((↑) : Real -> Complex) (hasSum_zeta_nat hk).tsum_eq
  · rw [← Nat.cast_two, ← Nat.cast_mul, zeta_nat_eq_tsum_of_gt_one (by lia)]
    simp [push_cast]
  · norm_cast

中文:
定理 riemannZeta_two_mul_nat
  条件: {k : 自然数} (hk : k != 0)
  证明: by
  convert! congr_arg ((↑) : Real -> Complex) (hasSum_zeta_nat hk).tsum_eq
  · rw [← Nat.cast_two, ← Nat.cast_mul, zeta_nat_eq_tsum_of_gt_one (by lia)]
    simp [push_cast]
  · norm_cast

Depends on / 依赖: Nat.cast_mul, Nat.cast_two, cast_mul, cast_two, congr_arg, convert, hasSum_zeta_nat, tsum_eq, zeta_nat_eq_tsum_of_gt_one
-/
theorem riemannZeta_two_mul_nat {k : Nat} (hk : k != 0) :
    riemannZeta (2 * k) = (-1) ^ (k + 1) * (2 : Complex) ^ (2 * k - 1)
      * (π : Complex) ^ (2 * k) * bernoulli (2 * k) / (2 * k)! := by
  convert! congr_arg ((↑) : Real -> Complex) (hasSum_zeta_nat hk).tsum_eq
  · rw [← Nat.cast_two, ← Nat.cast_mul, zeta_nat_eq_tsum_of_gt_one (by lia)]
    simp [push_cast]
  · norm_cast

/--
theorem `riemannZeta_two_mul_nat'` / 定理 `riemannZeta_two_mul_nat'`

English:
theorem riemannZeta_two_mul_nat'
  given: {k : Nat}
  proof: by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [riemannZeta_zero]
    norm_num
  · convert riemannZeta_two_mul_nat hk
    grind [zpow_natCast]

中文:
定理 riemannZeta_two_mul_nat'
  条件: {k : 自然数}
  证明: by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [riemannZeta_zero]
    norm_num
  · convert riemannZeta_two_mul_nat hk
    grind [zpow_natCast]

Depends on / 依赖: convert, eq_or_ne, riemannZeta_two_mul_nat, riemannZeta_zero, zpow_natCast
-/
theorem riemannZeta_two_mul_nat' {k : Nat} :
    riemannZeta (2 * k) = (-1) ^ (k + 1) * (2 : Complex) ^ (2 * k - 1 : Int)
      * (π : Complex) ^ (2 * k) * bernoulli (2 * k) / (2 * k)! := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [riemannZeta_zero]
    norm_num
  · convert riemannZeta_two_mul_nat hk
    grind [zpow_natCast]

/--
theorem `riemannZeta_two` / 定理 `riemannZeta_two`

English:
theorem riemannZeta_two
  statement: riemannZeta 2 = (π : Complex) ^ 2 / 6
  proof: by
  convert! congr_arg ((↑) : Real -> Complex) hasSum_zeta_two.tsum_eq
  · rw [← Nat.cast_two, zeta_nat_eq_tsum_of_gt_one one_lt_two]
    simp [push_cast]
  · norm_cast

中文:
定理 riemannZeta_two
  结论: riemannZeta 2 = (π : 复形) ^ 2 / 6
  证明: by
  convert! congr_arg ((↑) : Real -> Complex) hasSum_zeta_two.tsum_eq
  · rw [← Nat.cast_two, zeta_nat_eq_tsum_of_gt_one one_lt_two]
    simp [push_cast]
  · norm_cast

Depends on / 依赖: Nat.cast_two, cast_two, congr_arg, convert, hasSum_zeta_two, hasSum_zeta_two.tsum_eq, one_lt_two, tsum_eq, zeta_nat_eq_tsum_of_gt_one
-/
theorem riemannZeta_two : riemannZeta 2 = (π : Complex) ^ 2 / 6 := by
  convert! congr_arg ((↑) : Real -> Complex) hasSum_zeta_two.tsum_eq
  · rw [← Nat.cast_two, zeta_nat_eq_tsum_of_gt_one one_lt_two]
    simp [push_cast]
  · norm_cast

/--
theorem `riemannZeta_four` / 定理 `riemannZeta_four`

English:
theorem riemannZeta_four
  statement: riemannZeta 4 = π ^ 4 / 90
  proof: by
  convert! congr_arg ((↑) : Real -> Complex) hasSum_zeta_four.tsum_eq
  · rw [← Nat.cast_one, show (4 : Complex) = (4 : Nat) by simp,
      zeta_nat_eq_tsum_of_gt_one (by simp : 1 < 4)]
    simp only [push_cast]
  · norm_cast

中文:
定理 riemannZeta_four
  结论: riemannZeta 4 = π ^ 4 / 90
  证明: by
  convert! congr_arg ((↑) : Real -> Complex) hasSum_zeta_four.tsum_eq
  · rw [← Nat.cast_one, show (4 : Complex) = (4 : Nat) by simp,
      zeta_nat_eq_tsum_of_gt_one (by simp : 1 < 4)]
    simp only [push_cast]
  · norm_cast

Depends on / 依赖: Nat.cast_one, cast_one, congr_arg, convert, hasSum_zeta_four, hasSum_zeta_four.tsum_eq, tsum_eq, zeta_nat_eq_tsum_of_gt_one
-/
theorem riemannZeta_four : riemannZeta 4 = π ^ 4 / 90 := by
  convert! congr_arg ((↑) : Real -> Complex) hasSum_zeta_four.tsum_eq
  · rw [← Nat.cast_one, show (4 : Complex) = (4 : Nat) by simp,
      zeta_nat_eq_tsum_of_gt_one (by simp : 1 < 4)]
    simp only [push_cast]
  · norm_cast

/--
theorem `riemannZeta_neg_nat_eq_bernoulli'` / 定理 `riemannZeta_neg_nat_eq_bernoulli'`

English:
theorem riemannZeta_neg_nat_eq_bernoulli'
  given: (k : Nat)
  proof: by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [Nat.cast_zero, neg_zero, riemannZeta_zero, zero_add, zero_add, div_one,
      bernoulli'_one, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, neg_div]
  · rw [← hurwitzZeta_zero, ← QuotientAddGroup.mk_zero, hurwitzZeta_neg_nat hk
      (left_mem_Icc.mpr zero_le_one), ofReal_zero, Polynomial.eval_zero_map,
      Polynomial.bernoulli_eval_zero, Algebra.algebraMap_eq_smul_one, Rat.smul_one_eq_cast,
      div_mul_eq_mul_div, neg_one_mul, bernoulli_eq_bernoulli'_of_ne_one (by simp [hk])]

中文:
定理 riemannZeta_neg_nat_eq_bernoulli'
  条件: (k : 自然数)
  证明: by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [Nat.cast_zero, neg_zero, riemannZeta_zero, zero_add, zero_add, div_one,
      bernoulli'_one, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, neg_div]
  · rw [← hurwitzZeta_zero, ← QuotientAddGroup.mk_zero, hurwitzZeta_neg_nat hk
      (left_mem_Icc.mpr zero_le_one), ofReal_zero, Polynomial.eval_zero_map,
      Polynomial.bernoulli_eval_zero, Algebra.algebraMap_eq_smul_one, Rat.smul_one_eq_cast,
      div_mul_eq_mul_div, neg_one_mul, bernoulli_eq_bernoulli'_of_ne_one (by simp [hk])]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, Nat.cast_zero, Polynomial, Polynomial.bernoulli_eval_zero, Polynomial.eval_zero_map, QuotientAddGroup, QuotientAddGroup.mk_zero, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.smul_one_eq_cast, _of_ne_one, _one, algebraMap_eq_smul_one, bernoulli, bernoulli_eq_bernoulli, bernoulli_eval_zero, cast_div, cast_ofNat
-/
theorem riemannZeta_neg_nat_eq_bernoulli' (k : Nat) :
    riemannZeta (-k) = -bernoulli' (k + 1) / (k + 1) := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [Nat.cast_zero, neg_zero, riemannZeta_zero, zero_add, zero_add, div_one,
      bernoulli'_one, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, neg_div]
  · rw [← hurwitzZeta_zero, ← QuotientAddGroup.mk_zero, hurwitzZeta_neg_nat hk
      (left_mem_Icc.mpr zero_le_one), ofReal_zero, Polynomial.eval_zero_map,
      Polynomial.bernoulli_eval_zero, Algebra.algebraMap_eq_smul_one, Rat.smul_one_eq_cast,
      div_mul_eq_mul_div, neg_one_mul, bernoulli_eq_bernoulli'_of_ne_one (by simp [hk])]

/--
theorem `riemannZeta_neg_nat_eq_bernoulli` / 定理 `riemannZeta_neg_nat_eq_bernoulli`

English:
theorem riemannZeta_neg_nat_eq_bernoulli
  given: (k : Nat)
  proof: by
  rw [riemannZeta_neg_nat_eq_bernoulli']; rw [bernoulli]; rw [Rat.cast_mul]; rw [Rat.cast_pow]; rw [Rat.cast_neg]; rw [Rat.cast_one]; rw [← neg_one_mul]; rw [← mul_assoc]; rw [pow_succ]; rw [← mul_assoc]; rw [← mul_pow]; rw [neg_one_mul (-1)]; rw [neg_neg]; rw [one_pow]; rw [one_mul]

中文:
定理 riemannZeta_neg_nat_eq_bernoulli
  条件: (k : 自然数)
  证明: by
  rw [riemannZeta_neg_nat_eq_bernoulli']; rw [bernoulli]; rw [Rat.cast_mul]; rw [Rat.cast_pow]; rw [Rat.cast_neg]; rw [Rat.cast_one]; rw [← neg_one_mul]; rw [← mul_assoc]; rw [pow_succ]; rw [← mul_assoc]; rw [← mul_pow]; rw [neg_one_mul (-1)]; rw [neg_neg]; rw [one_pow]; rw [one_mul]

Depends on / 依赖: Rat.cast_mul, Rat.cast_neg, Rat.cast_one, Rat.cast_pow, bernoulli, cast_mul, cast_neg, cast_one, cast_pow, mul_assoc, mul_pow, neg_neg, neg_one_mul, one_mul, one_pow, pow_succ, riemannZeta_neg_nat_eq_bernoulli
-/
theorem riemannZeta_neg_nat_eq_bernoulli (k : Nat) :
    riemannZeta (-k) = (-1 : Complex) ^ k * bernoulli (k + 1) / (k + 1) := by
  rw [riemannZeta_neg_nat_eq_bernoulli']; rw [bernoulli]; rw [Rat.cast_mul]; rw [Rat.cast_pow]; rw [Rat.cast_neg]; rw [Rat.cast_one]; rw [← neg_one_mul]; rw [← mul_assoc]; rw [pow_succ]; rw [← mul_assoc]; rw [← mul_pow]; rw [neg_one_mul (-1)]; rw [neg_neg]; rw [one_pow]; rw [one_mul]
