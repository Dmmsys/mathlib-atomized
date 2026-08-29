/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Analysis.Quaternion
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Lemmas about `NormedSpace.exp` on `Quaternion`s

This file contains results about `NormedSpace.exp` on `Quaternion ℝ`.

## Main results

* `Quaternion.exp_eq`: the general expansion of the quaternion exponential in terms of `Real.cos`
  and `Real.sin`.
* `Quaternion.exp_of_re_eq_zero`: the special case when the quaternion has a zero real part.
* `Quaternion.norm_exp`: the norm of the quaternion exponential is the norm of the exponential of
  the real part.

-/

public section

open scoped Quaternion Nat

open NormedSpace

namespace Quaternion

@[simp, norm_cast]
/--
theorem `exp_coe` / 定理 `exp_coe`

English:
theorem exp_coe
  given: (r : Real)
  statement: exp (r : ℍ[Real]) = ↑(exp r)
  proof: (map_exp (algebraMap Real ℍ[Real]) (continuous_algebraMap _ _) _).symm

中文:
定理 exp_coe
  条件: (r : 实数)
  结论: exp (r : ℍ[实数]) = ↑(exp r)
  证明: (map_exp (algebraMap Real ℍ[Real]) (continuous_algebraMap _ _) _).symm

Depends on / 依赖: algebraMap, continuous_algebraMap, map_exp
-/
theorem exp_coe (r : Real) : exp (r : ℍ[Real]) = ↑(exp r) :=
  (map_exp (algebraMap Real ℍ[Real]) (continuous_algebraMap _ _) _).symm

/--
theorem `expSeries_even_of_imaginary` / 定理 `expSeries_even_of_imaginary`

English:
theorem expSeries_even_of_imaginary
  given: {q : Quaternion Real} (hq : q.re = 0) (n : Nat)
  proof: by
  rw [expSeries_apply_eq]
  have hq2 : q ^ 2 = -normSq q := sq_eq_neg_normSq.mpr hq
  let k : Real := ↑(2 * n)!
  calc
    k⁻¹ • q ^ (2 * n) = k⁻¹ • (-normSq q) ^ n := by rw [pow_mul, hq2]
    _ = k⁻¹ • ↑((-1 : Real) ^ n * ‖q‖ ^ (2 * n)) := ?_
    _ = ↑((-1 : Real) ^ n * ‖q‖ ^ (2 * n) / k) := ?_


中文:
定理 expSeries_even_of_imaginary
  条件: {q : Quaternion 实数} (hq : q.re = 0) (n : 自然数)
  证明: by
  rw [expSeries_apply_eq]
  have hq2 : q ^ 2 = -normSq q := sq_eq_neg_normSq.mpr hq
  let k : Real := ↑(2 * n)!
  calc
    k⁻¹ • q ^ (2 * n) = k⁻¹ • (-normSq q) ^ n := by rw [pow_mul, hq2]
    _ = k⁻¹ • ↑((-1 : Real) ^ n * ‖q‖ ^ (2 * n)) := ?_
    _ = ↑((-1 : Real) ^ n * ‖q‖ ^ (2 * n) / k) := ?_


Depends on / 依赖: coe_mul_eq_smul, div_eq_mul_inv, expSeries_apply_eq, neg_pow, normSq, normSq_eq_norm_mul_self, pow_mul, ring_nf, sq_eq_neg_normSq, sq_eq_neg_normSq.mpr
-/
theorem expSeries_even_of_imaginary {q : Quaternion Real} (hq : q.re = 0) (n : Nat) :
    expSeries Real (Quaternion Real) (2 * n) (fun _ => q) =
      ↑((-1 : Real) ^ n * ‖q‖ ^ (2 * n) / (2 * n)!) := by
  rw [expSeries_apply_eq]
  have hq2 : q ^ 2 = -normSq q := sq_eq_neg_normSq.mpr hq
  let k : Real := ↑(2 * n)!
  calc
    k⁻¹ • q ^ (2 * n) = k⁻¹ • (-normSq q) ^ n := by rw [pow_mul, hq2]
    _ = k⁻¹ • ↑((-1 : Real) ^ n * ‖q‖ ^ (2 * n)) := ?_
    _ = ↑((-1 : Real) ^ n * ‖q‖ ^ (2 * n) / k) := ?_
  · congr 1
    rw [neg_pow]; rw [normSq_eq_norm_mul_self]; rw [pow_mul]; rw [sq]
    push_cast
    rfl
  · rw [← coe_mul_eq_smul, div_eq_mul_inv]
    norm_cast
    ring_nf

/--
theorem `expSeries_odd_of_imaginary` / 定理 `expSeries_odd_of_imaginary`

English:
theorem expSeries_odd_of_imaginary
  given: {q : Quaternion Real} (hq : q.re = 0) (n : Nat)
  proof: by
  rw [expSeries_apply_eq]
  obtain rfl | hq0 := eq_or_ne q 0
  · simp
  have hq2 : q ^ 2 = -normSq q := sq_eq_neg_normSq.mpr hq
  have hqn := norm_ne_zero_iff.mpr hq0
  let k : Real := ↑(2 * n + 1)!
  calc
    k⁻¹ • q ^ (2 * n + 1) = k⁻¹ • ((-normSq q) ^ n * q) := by rw [pow_succ, pow_mul, hq2]
 

中文:
定理 expSeries_odd_of_imaginary
  条件: {q : Quaternion 实数} (hq : q.re = 0) (n : 自然数)
  证明: by
  rw [expSeries_apply_eq]
  obtain rfl | hq0 := eq_or_ne q 0
  · simp
  have hq2 : q ^ 2 = -normSq q := sq_eq_neg_normSq.mpr hq
  have hqn := norm_ne_zero_iff.mpr hq0
  let k : Real := ↑(2 * n + 1)!
  calc
    k⁻¹ • q ^ (2 * n + 1) = k⁻¹ • ((-normSq q) ^ n * q) := by rw [pow_succ, pow_mul, hq2]
 

Depends on / 依赖: coe_mul_eq_smul, eq_or_ne, expSeries_apply_eq, neg_pow, normSq, normSq_eq_norm_mul_self, norm_ne_zero_iff, norm_ne_zero_iff.mpr, pow_mul, pow_succ, sq_eq_neg_normSq, sq_eq_neg_normSq.mpr
-/
theorem expSeries_odd_of_imaginary {q : Quaternion Real} (hq : q.re = 0) (n : Nat) :
    expSeries Real (Quaternion Real) (2 * n + 1) (fun _ => q) =
      (((-1 : Real) ^ n * ‖q‖ ^ (2 * n + 1) / (2 * n + 1)!) / ‖q‖) • q := by
  rw [expSeries_apply_eq]
  obtain rfl | hq0 := eq_or_ne q 0
  · simp
  have hq2 : q ^ 2 = -normSq q := sq_eq_neg_normSq.mpr hq
  have hqn := norm_ne_zero_iff.mpr hq0
  let k : Real := ↑(2 * n + 1)!
  calc
    k⁻¹ • q ^ (2 * n + 1) = k⁻¹ • ((-normSq q) ^ n * q) := by rw [pow_succ, pow_mul, hq2]
    _ = k⁻¹ • ((-1 : Real) ^ n * ‖q‖ ^ (2 * n)) • q := ?_
    _ = ((-1 : Real) ^ n * ‖q‖ ^ (2 * n + 1) / k / ‖q‖) • q := ?_
  · congr 1
    rw [neg_pow]; rw [normSq_eq_norm_mul_self]; rw [pow_mul]; rw [sq]; rw [← coe_mul_eq_smul]
    norm_cast
  · rw [smul_smul]
    congr 1
    simp_rw [pow_succ, mul_div_assoc, div_div_cancel_left' hqn]
    ring

/--
theorem `hasSum_expSeries_of_imaginary` / 定理 `hasSum_expSeries_of_imaginary`

English:
theorem hasSum_expSeries_of_imaginary
  statement: {q : Quaternion Real} (hq : q.re = 0) {c s : Real}
  proof: by
  replace hc := hasSum_coe.mpr hc
  replace hs := (hs.div_const ‖q‖).smul_const q
  refine HasSum.even_add_odd ?_ ?_
  · convert! hc using 1
    ext n : 1
    rw [expSeries_even_of_imaginary hq]
  · convert! hs using 1
    ext n : 1
    rw [expSeries_odd_of_imaginary hq]

中文:
定理 hasSum_expSeries_of_imaginary
  结论: {q : Quaternion 实数} (hq : q.re = 0) {c s : 实数}
  证明: by
  replace hc := hasSum_coe.mpr hc
  replace hs := (hs.div_const ‖q‖).smul_const q
  refine HasSum.even_add_odd ?_ ?_
  · convert! hc using 1
    ext n : 1
    rw [expSeries_even_of_imaginary hq]
  · convert! hs using 1
    ext n : 1
    rw [expSeries_odd_of_imaginary hq]

Depends on / 依赖: HasSum, HasSum.even_add_odd, convert, div_const, even_add_odd, expSeries_even_of_imaginary, expSeries_odd_of_imaginary, hasSum_coe, hasSum_coe.mpr, hs.div_const, replace, smul_const
-/
theorem hasSum_expSeries_of_imaginary {q : Quaternion Real} (hq : q.re = 0) {c s : Real}
    (hc : HasSum (fun n => (-1 : Real) ^ n * ‖q‖ ^ (2 * n) / (2 * n)!) c)
    (hs : HasSum (fun n => (-1 : Real) ^ n * ‖q‖ ^ (2 * n + 1) / (2 * n + 1)!) s) :
    HasSum (fun n => expSeries Real (Quaternion Real) n fun _ => q) (↑c + (s / ‖q‖) • q) := by
  replace hc := hasSum_coe.mpr hc
  replace hs := (hs.div_const ‖q‖).smul_const q
  refine HasSum.even_add_odd ?_ ?_
  · convert! hc using 1
    ext n : 1
    rw [expSeries_even_of_imaginary hq]
  · convert! hs using 1
    ext n : 1
    rw [expSeries_odd_of_imaginary hq]

set_option backward.isDefEq.respectTransparency false in -- This is needed or we get errors in later declarations.
/--
theorem `exp_of_re_eq_zero` / 定理 `exp_of_re_eq_zero`

English:
theorem exp_of_re_eq_zero
  given: (q : Quaternion Real) (hq : q.re = 0)
  proof: by
  rw [exp_eq_tsum Real]
  refine HasSum.tsum_eq ?_
  simp_rw [← expSeries_apply_eq]
  exact hasSum_expSeries_of_imaginary hq (Real.hasSum_cos _) (Real.hasSum_sin _)

中文:
定理 exp_of_re_eq_zero
  条件: (q : Quaternion 实数) (hq : q.re = 0)
  证明: by
  rw [exp_eq_tsum Real]
  refine HasSum.tsum_eq ?_
  simp_rw [← expSeries_apply_eq]
  exact hasSum_expSeries_of_imaginary hq (Real.hasSum_cos _) (Real.hasSum_sin _)

Depends on / 依赖: HasSum, HasSum.tsum_eq, Real.hasSum_cos, Real.hasSum_sin, expSeries_apply_eq, exp_eq_tsum, hasSum_cos, hasSum_expSeries_of_imaginary, hasSum_sin, simp_rw, tsum_eq
-/
theorem exp_of_re_eq_zero (q : Quaternion Real) (hq : q.re = 0) :
    exp q = ↑(Real.cos ‖q‖) + (Real.sin ‖q‖ / ‖q‖) • q := by
  rw [exp_eq_tsum Real]
  refine HasSum.tsum_eq ?_
  simp_rw [← expSeries_apply_eq]
  exact hasSum_expSeries_of_imaginary hq (Real.hasSum_cos _) (Real.hasSum_sin _)

set_option backward.isDefEq.respectTransparency false in -- This is needed or we get errors in later declarations.
/--
theorem `exp_eq` / 定理 `exp_eq`

English:
theorem exp_eq
  given: (q : Quaternion Real)
  proof: by
  let +nondep : NormedAlgebra Rat ℍ := .restrictScalars Rat Real ℍ
  rw [← exp_of_re_eq_zero q.im q.re_im]; rw [← coe_mul_eq_smul]; rw [← exp_coe]; rw [← exp_add_of_commute]; rw [re_add_im]
  exact Algebra.commutes q.re (_ : ℍ[Real])

中文:
定理 exp_eq
  条件: (q : Quaternion 实数)
  证明: by
  let +nondep : NormedAlgebra Rat ℍ := .restrictScalars Rat Real ℍ
  rw [← exp_of_re_eq_zero q.im q.re_im]; rw [← coe_mul_eq_smul]; rw [← exp_coe]; rw [← exp_add_of_commute]; rw [re_add_im]
  exact Algebra.commutes q.re (_ : ℍ[Real])

Depends on / 依赖: Algebra, Algebra.commutes, NormedAlgebra, coe_mul_eq_smul, commutes, exp_add_of_commute, exp_coe, exp_of_re_eq_zero, nondep, q.im, q.re, q.re_im, re_add_im, re_im, restrictScalars
-/
theorem exp_eq (q : Quaternion Real) :
    exp q = exp q.re • (↑(Real.cos ‖q.im‖) + (Real.sin ‖q.im‖ / ‖q.im‖) • q.im) := by
  let +nondep : NormedAlgebra Rat ℍ := .restrictScalars Rat Real ℍ
  rw [← exp_of_re_eq_zero q.im q.re_im]; rw [← coe_mul_eq_smul]; rw [← exp_coe]; rw [← exp_add_of_commute]; rw [re_add_im]
  exact Algebra.commutes q.re (_ : ℍ[Real])

/--
theorem `re_exp` / 定理 `re_exp`

English:
theorem re_exp
  given: (q : ℍ[Real])
  statement: (exp q).re = exp q.re * Real.cos ‖q - q.re‖
  proof: by simp [exp_eq]

中文:
定理 re_exp
  条件: (q : ℍ[实数])
  结论: (exp q).re = exp q.re * 实数.cos ‖q - q.re‖
  证明: by simp [exp_eq]

Depends on / 依赖: exp_eq
-/
theorem re_exp (q : ℍ[Real]) : (exp q).re = exp q.re * Real.cos ‖q - q.re‖ := by simp [exp_eq]

/--
theorem `im_exp` / 定理 `im_exp`

English:
theorem im_exp
  given: (q : ℍ[Real])
  statement: (exp q).im = (exp q.re * (Real.sin ‖q.im‖ / ‖q.im‖)) • q.im
  proof: by
  simp [exp_eq, smul_smul]

中文:
定理 im_exp
  条件: (q : ℍ[实数])
  结论: (exp q).im = (exp q.re * (实数.sin ‖q.im‖ / ‖q.im‖)) • q.im
  证明: by
  simp [exp_eq, smul_smul]

Depends on / 依赖: exp_eq, smul_smul
-/
theorem im_exp (q : ℍ[Real]) : (exp q).im = (exp q.re * (Real.sin ‖q.im‖ / ‖q.im‖)) • q.im := by
  simp [exp_eq, smul_smul]

/--
theorem `normSq_exp` / 定理 `normSq_exp`

English:
theorem normSq_exp
  given: (q : ℍ[Real])
  statement: normSq (exp q) = exp q.re ^ 2
  proof: calc
    normSq (exp q) =
        normSq (exp q.re • (↑(Real.cos ‖q.im‖) + (Real.sin ‖q.im‖ / ‖q.im‖) • q.im)) := by
      rw [exp_eq]
    _ = exp q.re ^ 2 * normSq (↑(Real.cos ‖q.im‖) + (Real.sin ‖q.im‖ / ‖q.im‖) • q.im) := by
      rw [normSq_smul]
    _ = exp q.re ^ 2 * (Real.cos ‖q.im‖ ^ 2 + Rea

中文:
定理 normSq_exp
  条件: (q : ℍ[实数])
  结论: normSq (exp q) = exp q.re ^ 2
  证明: calc
    normSq (exp q) =
        normSq (exp q.re • (↑(Real.cos ‖q.im‖) + (Real.sin ‖q.im‖ / ‖q.im‖) • q.im)) := by
      rw [exp_eq]
    _ = exp q.re ^ 2 * normSq (↑(Real.cos ‖q.im‖) + (Real.sin ‖q.im‖ / ‖q.im‖) • q.im) := by
      rw [normSq_smul]
    _ = exp q.re ^ 2 * (Real.cos ‖q.im‖ ^ 2 + Rea

Depends on / 依赖: Real.cos, Real.sin, coe_mul_eq_smul, eq_or_ne, exp_eq, normSq, normSq_add, normSq_smul, q.im, q.re, re_im, re_smul, re_star, smul_, smul_zero, star_smul
-/
theorem normSq_exp (q : ℍ[Real]) : normSq (exp q) = exp q.re ^ 2 :=
  calc
    normSq (exp q) =
        normSq (exp q.re • (↑(Real.cos ‖q.im‖) + (Real.sin ‖q.im‖ / ‖q.im‖) • q.im)) := by
      rw [exp_eq]
    _ = exp q.re ^ 2 * normSq (↑(Real.cos ‖q.im‖) + (Real.sin ‖q.im‖ / ‖q.im‖) • q.im) := by
      rw [normSq_smul]
    _ = exp q.re ^ 2 * (Real.cos ‖q.im‖ ^ 2 + Real.sin ‖q.im‖ ^ 2) := by
      congr 1
      obtain hv | hv := eq_or_ne ‖q.im‖ 0
      · simp [hv]
      rw [normSq_add]; rw [normSq_smul]; rw [star_smul]; rw [coe_mul_eq_smul]; rw [re_smul]; rw [re_smul]; rw [re_star]; rw [re_im]; rw [smul_zero]; rw [smul_zero]; rw [mul_zero]; rw [add_zero]; rw [div_pow]; rw [normSq_coe]; rw [normSq_eq_norm_mul_self]; rw [← sq]; rw [div_mul_cancel₀ _ (pow_ne_zero _ hv)]
    _ = exp q.re ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]

/-- Note that this implies that exponentials of pure imaginary quaternions are unit quaternions
since in that case the RHS is `1` via `NormedSpace.exp_zero` and `norm_one`. -/
@[simp]
/--
theorem `norm_exp` / 定理 `norm_exp`

English:
theorem norm_exp
  given: (q : ℍ[Real])
  statement: ‖exp q‖ = ‖exp q.re‖
  proof: by
  rw [norm_eq_sqrt_real_inner (exp q)]; rw [inner_self]; rw [normSq_exp]; rw [Real.sqrt_sq_eq_abs]; rw [Real.norm_eq_abs]

中文:
定理 norm_exp
  条件: (q : ℍ[实数])
  结论: ‖exp q‖ = ‖exp q.re‖
  证明: by
  rw [norm_eq_sqrt_real_inner (exp q)]; rw [inner_self]; rw [normSq_exp]; rw [Real.sqrt_sq_eq_abs]; rw [Real.norm_eq_abs]

Depends on / 依赖: Real.norm_eq_abs, Real.sqrt_sq_eq_abs, inner_self, normSq_exp, norm_eq_abs, norm_eq_sqrt_real_inner, sqrt_sq_eq_abs
-/
theorem norm_exp (q : ℍ[Real]) : ‖exp q‖ = ‖exp q.re‖ := by
  rw [norm_eq_sqrt_real_inner (exp q)]; rw [inner_self]; rw [normSq_exp]; rw [Real.sqrt_sq_eq_abs]; rw [Real.norm_eq_abs]

end Quaternion
