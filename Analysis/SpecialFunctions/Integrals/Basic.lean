/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.NonIntegrable
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.SpecialFunctions.Log.InvLog
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Integration of specific interval integrals

This file contains proofs of the integrals of various specific functions. This includes:
* Integrals of simple functions, such as `id`, `pow`, `inv`, `exp`, `log`
* Integrals of some trigonometric functions, such as `sin`, `cos`, `1 / (1 + x^2)`
* The integral of `cos x ^ 2 - sin x ^ 2`
* Reduction formulae for the integrals of `sin x ^ n` and `cos x ^ n` for `n ≥ 2`
* The computation of `∫ x in 0..π, sin x ^ n` as a product for even and odd `n` (used in proving the
  Wallis product for pi)
* Integrals of the form `sin x ^ m * cos x ^ n`

With these lemmas, many simple integrals can be computed by `simp` or `norm_num`.

This file is still being developed.

## Tags

integrate, integration, integrable
-/

public section


open Real Set Finset

open scoped Real Interval

variable {a b : Real} (n : Nat)

namespace intervalIntegral

open MeasureTheory

variable {f : Real -> Real} {μ : Measure Real} [IsLocallyFiniteMeasure μ] (c d : Real)

/-! ### Integrals of the form `c * ∫ x in a..b, f (c * x + d)` -/
section

@[simp]
/--
theorem `mul_integral_comp_mul_right` / 定理 `mul_integral_comp_mul_right`

English:
theorem mul_integral_comp_mul_right
  statement: (c * ∫ x in a..b, f (x * c)) = ∫ x in a * c..b * c, f x
  proof: smul_integral_comp_mul_right f c

@[simp]

中文:
定理 mul_integral_comp_mul_right
  结论: (c * ∫ x in a..b, f (x * c)) = ∫ x in a * c..b * c, f x
  证明: smul_integral_comp_mul_right f c

@[simp]

Depends on / 依赖: smul_integral_comp_mul_right
-/
theorem mul_integral_comp_mul_right : (c * ∫ x in a..b, f (x * c)) = ∫ x in a * c..b * c, f x :=
  smul_integral_comp_mul_right f c

@[simp]
/--
theorem `mul_integral_comp_mul_left` / 定理 `mul_integral_comp_mul_left`

English:
theorem mul_integral_comp_mul_left
  statement: (c * ∫ x in a..b, f (c * x)) = ∫ x in c * a..c * b, f x
  proof: smul_integral_comp_mul_left f c

@[simp]

中文:
定理 mul_integral_comp_mul_left
  结论: (c * ∫ x in a..b, f (c * x)) = ∫ x in c * a..c * b, f x
  证明: smul_integral_comp_mul_left f c

@[simp]

Depends on / 依赖: smul_integral_comp_mul_left
-/
theorem mul_integral_comp_mul_left : (c * ∫ x in a..b, f (c * x)) = ∫ x in c * a..c * b, f x :=
  smul_integral_comp_mul_left f c

@[simp]
/--
theorem `inv_mul_integral_comp_div` / 定理 `inv_mul_integral_comp_div`

English:
theorem inv_mul_integral_comp_div
  statement: (c⁻¹ * ∫ x in a..b, f (x / c)) = ∫ x in a / c..b / c, f x
  proof: inv_smul_integral_comp_div f c

@[simp]

中文:
定理 inv_mul_integral_comp_div
  结论: (c⁻¹ * ∫ x in a..b, f (x / c)) = ∫ x in a / c..b / c, f x
  证明: inv_smul_integral_comp_div f c

@[simp]

Depends on / 依赖: inv_smul_integral_comp_div
-/
theorem inv_mul_integral_comp_div : (c⁻¹ * ∫ x in a..b, f (x / c)) = ∫ x in a / c..b / c, f x :=
  inv_smul_integral_comp_div f c

@[simp]
/--
theorem `mul_integral_comp_mul_add` / 定理 `mul_integral_comp_mul_add`

English:
theorem mul_integral_comp_mul_add
  proof: smul_integral_comp_mul_add f c d

@[simp]

中文:
定理 mul_integral_comp_mul_add
  证明: smul_integral_comp_mul_add f c d

@[simp]

Depends on / 依赖: smul_integral_comp_mul_add
-/
theorem mul_integral_comp_mul_add :
    (c * ∫ x in a..b, f (c * x + d)) = ∫ x in c * a + d..c * b + d, f x :=
  smul_integral_comp_mul_add f c d

@[simp]
/--
theorem `mul_integral_comp_add_mul` / 定理 `mul_integral_comp_add_mul`

English:
theorem mul_integral_comp_add_mul
  proof: smul_integral_comp_add_mul f c d

@[simp]

中文:
定理 mul_integral_comp_add_mul
  证明: smul_integral_comp_add_mul f c d

@[simp]

Depends on / 依赖: smul_integral_comp_add_mul
-/
theorem mul_integral_comp_add_mul :
    (c * ∫ x in a..b, f (d + c * x)) = ∫ x in d + c * a..d + c * b, f x :=
  smul_integral_comp_add_mul f c d

@[simp]
/--
theorem `inv_mul_integral_comp_div_add` / 定理 `inv_mul_integral_comp_div_add`

English:
theorem inv_mul_integral_comp_div_add
  proof: inv_smul_integral_comp_div_add f c d

@[simp]

中文:
定理 inv_mul_integral_comp_div_add
  证明: inv_smul_integral_comp_div_add f c d

@[simp]

Depends on / 依赖: inv_smul_integral_comp_div_add
-/
theorem inv_mul_integral_comp_div_add :
    (c⁻¹ * ∫ x in a..b, f (x / c + d)) = ∫ x in a / c + d..b / c + d, f x :=
  inv_smul_integral_comp_div_add f c d

@[simp]
/--
theorem `inv_mul_integral_comp_add_div` / 定理 `inv_mul_integral_comp_add_div`

English:
theorem inv_mul_integral_comp_add_div
  proof: inv_smul_integral_comp_add_div f c d

@[simp]

中文:
定理 inv_mul_integral_comp_add_div
  证明: inv_smul_integral_comp_add_div f c d

@[simp]

Depends on / 依赖: inv_smul_integral_comp_add_div
-/
theorem inv_mul_integral_comp_add_div :
    (c⁻¹ * ∫ x in a..b, f (d + x / c)) = ∫ x in d + a / c..d + b / c, f x :=
  inv_smul_integral_comp_add_div f c d

@[simp]
/--
theorem `mul_integral_comp_mul_sub` / 定理 `mul_integral_comp_mul_sub`

English:
theorem mul_integral_comp_mul_sub
  proof: smul_integral_comp_mul_sub f c d

@[simp]

中文:
定理 mul_integral_comp_mul_sub
  证明: smul_integral_comp_mul_sub f c d

@[simp]

Depends on / 依赖: smul_integral_comp_mul_sub
-/
theorem mul_integral_comp_mul_sub :
    (c * ∫ x in a..b, f (c * x - d)) = ∫ x in c * a - d..c * b - d, f x :=
  smul_integral_comp_mul_sub f c d

@[simp]
/--
theorem `mul_integral_comp_sub_mul` / 定理 `mul_integral_comp_sub_mul`

English:
theorem mul_integral_comp_sub_mul
  proof: smul_integral_comp_sub_mul f c d

@[simp]

中文:
定理 mul_integral_comp_sub_mul
  证明: smul_integral_comp_sub_mul f c d

@[simp]

Depends on / 依赖: smul_integral_comp_sub_mul
-/
theorem mul_integral_comp_sub_mul :
    (c * ∫ x in a..b, f (d - c * x)) = ∫ x in d - c * b..d - c * a, f x :=
  smul_integral_comp_sub_mul f c d

@[simp]
/--
theorem `inv_mul_integral_comp_div_sub` / 定理 `inv_mul_integral_comp_div_sub`

English:
theorem inv_mul_integral_comp_div_sub
  proof: inv_smul_integral_comp_div_sub f c d

@[simp]

中文:
定理 inv_mul_integral_comp_div_sub
  证明: inv_smul_integral_comp_div_sub f c d

@[simp]

Depends on / 依赖: inv_smul_integral_comp_div_sub
-/
theorem inv_mul_integral_comp_div_sub :
    (c⁻¹ * ∫ x in a..b, f (x / c - d)) = ∫ x in a / c - d..b / c - d, f x :=
  inv_smul_integral_comp_div_sub f c d

@[simp]
/--
theorem `inv_mul_integral_comp_sub_div` / 定理 `inv_mul_integral_comp_sub_div`

English:
theorem inv_mul_integral_comp_sub_div
  proof: inv_smul_integral_comp_sub_div f c d

中文:
定理 inv_mul_integral_comp_sub_div
  证明: inv_smul_integral_comp_sub_div f c d

Depends on / 依赖: inv_smul_integral_comp_sub_div
-/
theorem inv_mul_integral_comp_sub_div :
    (c⁻¹ * ∫ x in a..b, f (d - x / c)) = ∫ x in d - b / c..d - a / c, f x :=
  inv_smul_integral_comp_sub_div f c d

end

end intervalIntegral

open intervalIntegral



/--
theorem `integral_cpow` / 定理 `integral_cpow`

English:
theorem integral_cpow
  given: {r : Complex} (h : -1 < r.re ∨ r != -1 ∧ (0 : Real) ∉ [[a, b]])
  proof: by
  rw [sub_div]
  have hr : r + 1 != 0 := by
    rcases h with h | h
    · apply_fun Complex.re
      rw [Complex.add_re]; rw [Complex.one_re]; rw [Complex.zero_re]; rw [Ne]; rw [add_eq_zero_iff_eq_neg]
      exact h.ne'
    · rw [Ne, ← add_eq_zero_iff_eq_neg] at h; exact h.1
  by_cases hab : (0 :

中文:
定理 integral_cpow
  条件: {r : 复形} (h : -1 < r.re ∨ r != -1 ∧ (0 : 实数) ∉ [[a, b]])
  证明: by
  rw [sub_div]
  have hr : r + 1 != 0 := by
    rcases h with h | h
    · apply_fun Complex.re
      rw [Complex.add_re]; rw [Complex.one_re]; rw [Complex.zero_re]; rw [Ne]; rw [add_eq_zero_iff_eq_neg]
      exact h.ne'
    · rw [Ne, ← add_eq_zero_iff_eq_neg] at h; exact h.1
  by_cases hab : (0 :

Depends on / 依赖: Complex.add_re, Complex.one_re, Complex.re, Complex.zero_re, Or.inr, add_eq_zero_iff_eq, add_eq_zero_iff_eq_neg, add_re, apply_fun, contrapose, h.ne, hasDerivAt_ofReal_cpow_const, integral_eq_sub_of_hasDerivAt, intervalIntegrable_cpow, ne_of_mem_of_not_mem, one_re, sub_div, zero_re
-/
theorem integral_cpow {r : Complex} (h : -1 < r.re ∨ r != -1 ∧ (0 : Real) ∉ [[a, b]]) :
    (∫ x : Real in a..b, (x : Complex) ^ r) = ((b : Complex) ^ (r + 1) - (a : Complex) ^ (r + 1)) / (r + 1) := by
  rw [sub_div]
  have hr : r + 1 != 0 := by
    rcases h with h | h
    · apply_fun Complex.re
      rw [Complex.add_re]; rw [Complex.one_re]; rw [Complex.zero_re]; rw [Ne]; rw [add_eq_zero_iff_eq_neg]
      exact h.ne'
    · rw [Ne, ← add_eq_zero_iff_eq_neg] at h; exact h.1
  by_cases hab : (0 : Real) ∉ [[a, b]]
  · apply integral_eq_sub_of_hasDerivAt (fun x hx => ?_)
      (intervalIntegrable_cpow (r := r) <| Or.inr hab)
    refine hasDerivAt_ofReal_cpow_const' (ne_of_mem_of_not_mem hx hab) ?_
    contrapose hr; rwa [add_eq_zero_iff_eq_neg]
  replace h : -1 < r.re := by tauto
  suffices forall c : Real, (∫ x : Real in 0..c, (x : Complex) ^ r) =
      (c : Complex) ^ (r + 1) / (r + 1) - (0 : Complex) ^ (r + 1) / (r + 1) by
    rw [← integral_add_adjacent_intervals (@intervalIntegrable_cpow' a 0 r h)
      (@intervalIntegrable_cpow' 0 b r h)]; rw [integral_symm]; rw [this a]; rw [this b]; rw [Complex.zero_cpow hr]
    ring
  intro c
  apply integral_eq_sub_of_hasDeriv_right
  · refine ((Complex.continuous_ofReal_cpow_const ?_).div_const _).continuousOn
    rwa [Complex.add_re, Complex.one_re, ← neg_lt_iff_pos_add]
  · refine fun x hx => (hasDerivAt_ofReal_cpow_const' ?_ ?_).hasDerivWithinAt
    · rcases le_total c 0 with (hc | hc)
      · rw [max_eq_left hc] at hx; exact hx.2.ne
      · rw [min_eq_left hc] at hx; exact hx.1.ne'
    · contrapose hr; rw [hr]; ring
  · exact intervalIntegrable_cpow' h

/--
theorem `integral_rpow` / 定理 `integral_rpow`

English:
theorem integral_rpow
  given: {r : Real} (h : -1 < r ∨ r != -1 ∧ (0 : Real) ∉ [[a, b]])
  proof: by
  have h' : -1 < (r : Complex).re ∨ (r : Complex) != -1 ∧ (0 : Real) ∉ [[a, b]] := by
    cases h
    · left; rwa [Complex.ofReal_re]
    · right; rwa [← Complex.ofReal_one, ← Complex.ofReal_neg, Ne, Complex.ofReal_inj]
  have :
    (∫ x in a..b, (x : Complex) ^ (r : Complex)) = ((b : Complex) ^ 

中文:
定理 integral_rpow
  条件: {r : 实数} (h : -1 < r ∨ r != -1 ∧ (0 : 实数) ∉ [[a, b]])
  证明: by
  have h' : -1 < (r : Complex).re ∨ (r : Complex) != -1 ∧ (0 : Real) ∉ [[a, b]] := by
    cases h
    · left; rwa [Complex.ofReal_re]
    · right; rwa [← Complex.ofReal_one, ← Complex.ofReal_neg, Ne, Complex.ofReal_inj]
  have :
    (∫ x in a..b, (x : Complex) ^ (r : Complex)) = ((b : Complex) ^ 

Depends on / 依赖: Complex.ofReal_inj, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_re, Complex.re, Complex.re_ofReal_mul, Complex.real_smul, apply_fun, convert, integral_cpow, intervalIntegral_eq_integral_uIoc, ofReal_inj, ofReal_neg, ofReal_one, ofReal_re, re_ofReal_mul, real_smul, simp_rw
-/
theorem integral_rpow {r : Real} (h : -1 < r ∨ r != -1 ∧ (0 : Real) ∉ [[a, b]]) :
    ∫ x in a..b, x ^ r = (b ^ (r + 1) - a ^ (r + 1)) / (r + 1) := by
  have h' : -1 < (r : Complex).re ∨ (r : Complex) != -1 ∧ (0 : Real) ∉ [[a, b]] := by
    cases h
    · left; rwa [Complex.ofReal_re]
    · right; rwa [← Complex.ofReal_one, ← Complex.ofReal_neg, Ne, Complex.ofReal_inj]
  have :
    (∫ x in a..b, (x : Complex) ^ (r : Complex)) = ((b : Complex) ^ (r + 1 : Complex) - (a : Complex) ^ (r + 1 : Complex)) / (r + 1) :=
    integral_cpow h'
  apply_fun Complex.re at this; convert! this
  · simp_rw [intervalIntegral_eq_integral_uIoc, Complex.real_smul, Complex.re_ofReal_mul, rpow_def,
      ← RCLike.re_eq_complex_re, smul_eq_mul]
    rw [integral_re]
    refine intervalIntegrable_iff.mp ?_
    rcases h' with h' | h'
    · exact intervalIntegrable_cpow' h'
    · exact intervalIntegrable_cpow (Or.inr h'.2)
  · rw [(by push_cast; rfl : (r : Complex) + 1 = ((r + 1 : Real) : Complex))]
    simp_rw [div_eq_inv_mul, ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.sub_re, rpow_def]

/--
theorem `integral_zpow` / 定理 `integral_zpow`

English:
theorem integral_zpow
  given: {n : Int} (h : 0 <= n ∨ n != -1 ∧ (0 : Real) ∉ [[a, b]])
  proof: by
  replace h : -1 < (n : Real) ∨ (n : Real) != -1 ∧ (0 : Real) ∉ [[a, b]] := mod_cast h
  exact mod_cast integral_rpow h

@[simp]

中文:
定理 integral_zpow
  条件: {n : 整数} (h : 0 <= n ∨ n != -1 ∧ (0 : 实数) ∉ [[a, b]])
  证明: by
  replace h : -1 < (n : Real) ∨ (n : Real) != -1 ∧ (0 : Real) ∉ [[a, b]] := mod_cast h
  exact mod_cast integral_rpow h

@[simp]

Depends on / 依赖: integral_rpow, mod_cast, replace
-/
theorem integral_zpow {n : Int} (h : 0 <= n ∨ n != -1 ∧ (0 : Real) ∉ [[a, b]]) :
    ∫ x in a..b, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1) := by
  replace h : -1 < (n : Real) ∨ (n : Real) != -1 ∧ (0 : Real) ∉ [[a, b]] := mod_cast h
  exact mod_cast integral_rpow h

@[simp]
/--
theorem `integral_pow` / 定理 `integral_pow`

English:
theorem integral_pow
  statement: ∫ x in a..b, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1)
  proof: by
  simpa only [← Int.natCast_succ, zpow_natCast] using! integral_zpow (Or.inl n.cast_nonneg)

中文:
定理 integral_pow
  结论: ∫ x in a..b, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1)
  证明: by
  simpa only [← Int.natCast_succ, zpow_natCast] using! integral_zpow (Or.inl n.cast_nonneg)

Depends on / 依赖: Int.natCast_succ, Or.inl, cast_nonneg, integral_zpow, n.cast_nonneg, natCast_succ, zpow_natCast
-/
theorem integral_pow : ∫ x in a..b, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1) := by
  simpa only [← Int.natCast_succ, zpow_natCast] using! integral_zpow (Or.inl n.cast_nonneg)

/--
theorem `integral_pow_abs_sub_uIoc` / 定理 `integral_pow_abs_sub_uIoc`

English:
theorem integral_pow_abs_sub_uIoc
  statement: ∫ x in Ι a b, |x - a| ^ n = |b - a| ^ (n + 1) / (n + 1)
  proof: by
  rcases le_or_gt a b with hab | hab
  · calc
      ∫ x in Ι a b, |x - a| ^ n = ∫ x in a..b, |x - a| ^ n := by
        rw [uIoc_of_le hab]; rw [← integral_of_le hab]
      _ = ∫ x in 0..(b - a), x ^ n := by
        simp only [integral_comp_sub_right fun x => |x| ^ n, sub_self]
        refine inte

中文:
定理 integral_pow_abs_sub_uIoc
  结论: ∫ x in Ι a b, |x - a| ^ n = |b - a| ^ (n + 1) / (n + 1)
  证明: by
  rcases le_or_gt a b with hab | hab
  · calc
      ∫ x in Ι a b, |x - a| ^ n = ∫ x in a..b, |x - a| ^ n := by
        rw [uIoc_of_le hab]; rw [← integral_of_le hab]
      _ = ∫ x in 0..(b - a), x ^ n := by
        simp only [integral_comp_sub_right fun x => |x| ^ n, sub_self]
        refine inte

Depends on / 依赖: Pow.pow, abs_of_nonneg, integral_comp_sub_right, integral_congr, integral_of_le, le_or_gt, sub_nonneg, sub_self, uIcc_of_le, uIoc_of_le
-/
theorem integral_pow_abs_sub_uIoc : ∫ x in Ι a b, |x - a| ^ n = |b - a| ^ (n + 1) / (n + 1) := by
  rcases le_or_gt a b with hab | hab
  · calc
      ∫ x in Ι a b, |x - a| ^ n = ∫ x in a..b, |x - a| ^ n := by
        rw [uIoc_of_le hab]; rw [← integral_of_le hab]
      _ = ∫ x in 0..(b - a), x ^ n := by
        simp only [integral_comp_sub_right fun x => |x| ^ n, sub_self]
        refine integral_congr fun x hx => congr_arg₂ Pow.pow (abs_of_nonneg <| ?_) rfl
        rw [uIcc_of_le (sub_nonneg.2 hab)] at hx
        exact hx.1
      _ = |b - a| ^ (n + 1) / (n + 1) := by simp [abs_of_nonneg (sub_nonneg.2 hab)]
  · calc
      ∫ x in Ι a b, |x - a| ^ n = ∫ x in b..a, |x - a| ^ n := by
        rw [uIoc_of_ge hab.le]; rw [← integral_of_le hab.le]
      _ = ∫ x in b - a..0, (-x) ^ n := by
        simp only [integral_comp_sub_right fun x => |x| ^ n, sub_self]
        refine integral_congr fun x hx => congr_arg₂ Pow.pow (abs_of_nonpos <| ?_) rfl
        rw [uIcc_of_le (sub_nonpos.2 hab.le)] at hx
        exact hx.2
      _ = |b - a| ^ (n + 1) / (n + 1) := by
        simp [integral_comp_neg fun x => x ^ n, abs_of_neg (sub_neg.2 hab)]

@[simp]
/--
theorem `integral_id` / 定理 `integral_id`

English:
theorem integral_id
  statement: ∫ x in a..b, x = (b ^ 2 - a ^ 2) / 2
  proof: by
  have := @integral_pow a b 1
  norm_num at this
  exact this

中文:
定理 integral_id
  结论: ∫ x in a..b, x = (b ^ 2 - a ^ 2) / 2
  证明: by
  have := @integral_pow a b 1
  norm_num at this
  exact this

Depends on / 依赖: integral_pow
-/
theorem integral_id : ∫ x in a..b, x = (b ^ 2 - a ^ 2) / 2 := by
  have := @integral_pow a b 1
  norm_num at this
  exact this

/--
theorem `integral_one` / 定理 `integral_one`

English:
theorem integral_one
  statement: (∫ _ in a..b, (1 : Real)) = b - a
  proof: by
  simp only [mul_one, smul_eq_mul, integral_const]

中文:
定理 integral_one
  结论: (∫ _ in a..b, (1 : 实数)) = b - a
  证明: by
  simp only [mul_one, smul_eq_mul, integral_const]

Depends on / 依赖: Y.property, integral_const, mul_one, property, smul_eq_mul
-/
theorem integral_one : (∫ _ in a..b, (1 : Real)) = b - a := by
  simp only [mul_one, smul_eq_mul, integral_const]

/--
theorem `integral_const_on_unit_interval` / 定理 `integral_const_on_unit_interval`

English:
theorem integral_const_on_unit_interval
  statement: ∫ _ in a..a + 1, b = b
  proof: by simp

@[simp]

中文:
定理 integral_const_on_unit_interval
  结论: ∫ _ in a..a + 1, b = b
  证明: by simp

@[simp]
-/
theorem integral_const_on_unit_interval : ∫ _ in a..a + 1, b = b := by simp

@[simp]
/--
theorem `integral_inv` / 定理 `integral_inv`

English:
theorem integral_inv
  given: (h : (0 : Real) ∉ [[a, b]])
  statement: ∫ x in a..b, x⁻¹ = log (b / a)
  proof: by
  have h' := fun x (hx : x in [[a, b]]) => ne_of_mem_of_not_mem hx h
  rw [integral_deriv_eq_sub' _ deriv_log' (fun x hx => differentiableAt_log (h' x hx))
      (continuousOn_inv₀.mono <| subset_compl_singleton_iff.mpr h)]; rw [log_div (h' b right_mem_uIcc) (h' a left_mem_uIcc)]

@[simp]

中文:
定理 integral_inv
  条件: (h : (0 : 实数) ∉ [[a, b]])
  结论: ∫ x in a..b, x⁻¹ = log (b / a)
  证明: by
  have h' := fun x (hx : x in [[a, b]]) => ne_of_mem_of_not_mem hx h
  rw [integral_deriv_eq_sub' _ deriv_log' (fun x hx => differentiableAt_log (h' x hx))
      (continuousOn_inv₀.mono <| subset_compl_singleton_iff.mpr h)]; rw [log_div (h' b right_mem_uIcc) (h' a left_mem_uIcc)]

@[simp]

Depends on / 依赖: deriv_log, differentiableAt_log, integral_deriv_eq_sub, left_mem_uIcc, log_div, ne_of_mem_of_not_mem, right_mem_uIcc, subset_compl_singleton_iff, subset_compl_singleton_iff.mpr
-/
theorem integral_inv (h : (0 : Real) ∉ [[a, b]]) : ∫ x in a..b, x⁻¹ = log (b / a) := by
  have h' := fun x (hx : x in [[a, b]]) => ne_of_mem_of_not_mem hx h
  rw [integral_deriv_eq_sub' _ deriv_log' (fun x hx => differentiableAt_log (h' x hx))
      (continuousOn_inv₀.mono <| subset_compl_singleton_iff.mpr h)]; rw [log_div (h' b right_mem_uIcc) (h' a left_mem_uIcc)]

@[simp]
/--
theorem `integral_inv_of_pos` / 定理 `integral_inv_of_pos`

English:
theorem integral_inv_of_pos
  given: (ha : 0 < a) (hb : 0 < b)
  statement: ∫ x in a..b, x⁻¹ = log (b / a)
  proof: integral_inv notMem_uIcc_of_lt ha hb

@[simp]

中文:
定理 integral_inv_of_pos
  条件: (ha : 0 < a) (hb : 0 < b)
  结论: ∫ x in a..b, x⁻¹ = log (b / a)
  证明: integral_inv notMem_uIcc_of_lt ha hb

@[simp]

Depends on / 依赖: integral_inv, notMem_uIcc_of_lt
-/
theorem integral_inv_of_pos (ha : 0 < a) (hb : 0 < b) : ∫ x in a..b, x⁻¹ = log (b / a) :=
integral_inv notMem_uIcc_of_lt ha hb

@[simp]
/--
theorem `integral_inv_of_neg` / 定理 `integral_inv_of_neg`

English:
theorem integral_inv_of_neg
  given: (ha : a < 0) (hb : b < 0)
  statement: ∫ x in a..b, x⁻¹ = log (b / a)
  proof: integral_inv notMem_uIcc_of_gt ha hb

中文:
定理 integral_inv_of_neg
  条件: (ha : a < 0) (hb : b < 0)
  结论: ∫ x in a..b, x⁻¹ = log (b / a)
  证明: integral_inv notMem_uIcc_of_gt ha hb

Depends on / 依赖: integral_inv, notMem_uIcc_of_gt
-/
theorem integral_inv_of_neg (ha : a < 0) (hb : b < 0) : ∫ x in a..b, x⁻¹ = log (b / a) :=
integral_inv notMem_uIcc_of_gt ha hb

/--
theorem `integral_one_div` / 定理 `integral_one_div`

English:
theorem integral_one_div
  given: (h : (0 : Real) ∉ [[a, b]])
  statement: ∫ x : Real in a..b, 1 / x = log (b / a)
  proof: by
  simp only [one_div, integral_inv h]

中文:
定理 integral_one_div
  条件: (h : (0 : 实数) ∉ [[a, b]])
  结论: ∫ x : 实数 in a..b, 1 / x = log (b / a)
  证明: by
  simp only [one_div, integral_inv h]

Depends on / 依赖: integral_inv, one_div
-/
theorem integral_one_div (h : (0 : Real) ∉ [[a, b]]) : ∫ x : Real in a..b, 1 / x = log (b / a) := by
  simp only [one_div, integral_inv h]

/--
theorem `integral_one_div_of_pos` / 定理 `integral_one_div_of_pos`

English:
theorem integral_one_div_of_pos
  given: (ha : 0 < a) (hb : 0 < b)
  proof: by simp only [one_div, integral_inv_of_pos ha hb]

中文:
定理 integral_one_div_of_pos
  条件: (ha : 0 < a) (hb : 0 < b)
  证明: by simp only [one_div, integral_inv_of_pos ha hb]

Depends on / 依赖: integral_inv_of_pos, one_div
-/
theorem integral_one_div_of_pos (ha : 0 < a) (hb : 0 < b) :
    ∫ x : Real in a..b, 1 / x = log (b / a) := by simp only [one_div, integral_inv_of_pos ha hb]

/--
theorem `integral_one_div_of_neg` / 定理 `integral_one_div_of_neg`

English:
theorem integral_one_div_of_neg
  given: (ha : a < 0) (hb : b < 0)
  proof: by simp only [one_div, integral_inv_of_neg ha hb]

@[simp]

中文:
定理 integral_one_div_of_neg
  条件: (ha : a < 0) (hb : b < 0)
  证明: by simp only [one_div, integral_inv_of_neg ha hb]

@[simp]

Depends on / 依赖: integral_inv_of_neg, one_div
-/
theorem integral_one_div_of_neg (ha : a < 0) (hb : b < 0) :
    ∫ x : Real in a..b, 1 / x = log (b / a) := by simp only [one_div, integral_inv_of_neg ha hb]

@[simp]
/--
theorem `integral_exp` / 定理 `integral_exp`

English:
theorem integral_exp
  statement: ∫ x in a..b, exp x = exp b - exp a
  proof: by
  rw [integral_deriv_eq_sub']
  · simp
  · exact fun _ _ => differentiableAt_exp
  · exact continuousOn_exp

中文:
定理 integral_exp
  结论: ∫ x in a..b, exp x = exp b - exp a
  证明: by
  rw [integral_deriv_eq_sub']
  · simp
  · exact fun _ _ => differentiableAt_exp
  · exact continuousOn_exp

Depends on / 依赖: continuousOn_exp, differentiableAt_exp, integral_deriv_eq_sub
-/
theorem integral_exp : ∫ x in a..b, exp x = exp b - exp a := by
  rw [integral_deriv_eq_sub']
  · simp
  · exact fun _ _ => differentiableAt_exp
  · exact continuousOn_exp

/--
theorem `integral_exp_mul_complex` / 定理 `integral_exp_mul_complex`

English:
theorem integral_exp_mul_complex
  given: {c : Complex} (hc : c != 0)
  proof: by
  have D : forall x : Real, HasDerivAt (fun y : Real => Complex.exp (c * y) / c) (Complex.exp (c * x)) x := by
    intro x
    conv => congr
    rw [← mul_div_cancel_right₀ (Complex.exp (c * x)) hc]
    apply ((Complex.hasDerivAt_exp _).comp x _).div_const c
    simpa only [mul_one] using! ((hasD

中文:
定理 integral_exp_mul_complex
  条件: {c : 复形} (hc : c != 0)
  证明: by
  have D : forall x : Real, HasDerivAt (fun y : Real => Complex.exp (c * y) / c) (Complex.exp (c * x)) x := by
    intro x
    conv => congr
    rw [← mul_div_cancel_right₀ (Complex.exp (c * x)) hc]
    apply ((Complex.hasDerivAt_exp _).comp x _).div_const c
    simpa only [mul_one] using! ((hasD

Depends on / 依赖: Complex.exp, Complex.hasDerivAt_exp, HasDerivAt, comp_ofReal, const_mul, differentiableAt, div_const, fun_prop, hasDerivAt_exp, hasDerivAt_id, integral_deriv_eq_sub, mul_one
-/
theorem integral_exp_mul_complex {c : Complex} (hc : c != 0) :
    (∫ x in a..b, Complex.exp (c * x)) = (Complex.exp (c * b) - Complex.exp (c * a)) / c := by
  have D : forall x : Real, HasDerivAt (fun y : Real => Complex.exp (c * y) / c) (Complex.exp (c * x)) x := by
    intro x
    conv => congr
    rw [← mul_div_cancel_right₀ (Complex.exp (c * x)) hc]
    apply ((Complex.hasDerivAt_exp _).comp x _).div_const c
    simpa only [mul_one] using! ((hasDerivAt_id (x : Complex)).const_mul _).comp_ofReal
  rw [integral_deriv_eq_sub' _ (funext fun x => (D x).deriv) fun x _ => (D x).differentiableAt]
  · ring
  · fun_prop

/--
lemma `integral_exp_mul_I_eq_sin` / 引理 `integral_exp_mul_I_eq_sin`

English:
lemma integral_exp_mul_I_eq_sin
  given: (r : Real)
  proof: calc ∫ t in -r..r, Complex.exp (t * Complex.I)
  _ = (Complex.exp (Complex.I * r) - Complex.exp (Complex.I * (-r))) / Complex.I := by
    simp_rw [mul_comm _ Complex.I]
    rw [integral_exp_mul_complex]
    · simp
    · simp
  _ = 2 * Real.sin r := by
    simp only [mul_comm Complex.I, Complex.exp_m

中文:
引理 integral_exp_mul_I_eq_sin
  条件: (r : 实数)
  证明: calc ∫ t in -r..r, Complex.exp (t * Complex.I)
  _ = (Complex.exp (Complex.I * r) - Complex.exp (Complex.I * (-r))) / Complex.I := by
    simp_rw [mul_comm _ Complex.I]
    rw [integral_exp_mul_complex]
    · simp
    · simp
  _ = 2 * Real.sin r := by
    simp only [mul_comm Complex.I, Complex.exp_m

Depends on / 依赖: Complex.I, Complex.cos_neg, Complex.div_I, Complex.exp, Complex.exp_mul_I, Complex.ofReal_sin, Complex.sin_neg, Real.sin, add_sub_add_left_eq_sub, cos_neg, div_I, exp_mul_I, integral_exp_mul_complex, mul_assoc, mul_comm, ofReal_sin, simp_rw, sin_neg, sub_mul, two_mul
-/
lemma integral_exp_mul_I_eq_sin (r : Real) :
    ∫ t in -r..r, Complex.exp (t * Complex.I) = 2 * Real.sin r :=
  calc ∫ t in -r..r, Complex.exp (t * Complex.I)
  _ = (Complex.exp (Complex.I * r) - Complex.exp (Complex.I * (-r))) / Complex.I := by
    simp_rw [mul_comm _ Complex.I]
    rw [integral_exp_mul_complex]
    · simp
    · simp
  _ = 2 * Real.sin r := by
    simp only [mul_comm Complex.I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
      add_sub_add_left_eq_sub, Complex.div_I, Complex.ofReal_sin]
    rw [sub_mul]; rw [mul_assoc]; rw [mul_assoc]; rw [two_mul]
    simp

/--
lemma `integral_exp_mul_I_eq_sinc` / 引理 `integral_exp_mul_I_eq_sinc`

English:
lemma integral_exp_mul_I_eq_sinc
  given: (r : Real)
  proof: by
  rw [integral_exp_mul_I_eq_sin]
  by_cases hr : r = 0
  · simp [hr]
  rw [sinc_of_ne_zero hr]
  norm_cast
  field

中文:
引理 integral_exp_mul_I_eq_sinc
  条件: (r : 实数)
  证明: by
  rw [integral_exp_mul_I_eq_sin]
  by_cases hr : r = 0
  · simp [hr]
  rw [sinc_of_ne_zero hr]
  norm_cast
  field

Depends on / 依赖: integral_exp_mul_I_eq_sin, sinc_of_ne_zero
-/
lemma integral_exp_mul_I_eq_sinc (r : Real) :
    ∫ t in -r..r, Complex.exp (t * Complex.I) = 2 * r * sinc r := by
  rw [integral_exp_mul_I_eq_sin]
  by_cases hr : r = 0
  · simp [hr]
  rw [sinc_of_ne_zero hr]
  norm_cast
  field

/--
lemma `integral_log_from_zero_of_pos` / 引理 `integral_log_from_zero_of_pos`

English:
lemma integral_log_from_zero_of_pos
  given: (ht : 0 < b)
  statement: ∫ s in 0..b, log s = b * log b - b
  proof: by
  -- Compute the integral by giving a primitive and considering it limit as x approaches 0 from the
  -- right. The following lines were suggested by Gareth Ma on Zulip.
  rw [integral_eq_sub_of_hasDerivAt_of_tendsto (f := fun x => x * log x - x)
    (fa := 0) (fb := b * log b - b) (hint := inter

中文:
引理 integral_log_from_zero_of_pos
  条件: (ht : 0 < b)
  结论: ∫ s in 0..b, log s = b * log b - b
  证明: by
  -- Compute the integral by giving a primitive and considering it limit as x approaches 0 from the
  -- right. The following lines were suggested by Gareth Ma on Zulip.
  rw [integral_eq_sub_of_hasDerivAt_of_tendsto (f := fun x => x * log x - x)
    (fa := 0) (fb := b * log b - b) (hint := inter
-/
lemma integral_log_from_zero_of_pos (ht : 0 < b) : ∫ s in 0..b, log s = b * log b - b := by
  -- Compute the integral by giving a primitive and considering it limit as x approaches 0 from the
  -- right. The following lines were suggested by Gareth Ma on Zulip.
  rw [integral_eq_sub_of_hasDerivAt_of_tendsto (f := fun x => x * log x - x)
    (fa := 0) (fb := b * log b - b) (hint := intervalIntegrable_log')]
  · abel
  · exact ht
  · intro s ⟨hs, _ ⟩
    simpa using! (hasDerivAt_mul_log hs.ne.symm).sub (hasDerivAt_id s)
  · simpa [mul_comm] using! ((tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one).sub
      (tendsto_nhdsWithin_of_tendsto_nhds Filter.tendsto_id))
  · exact tendsto_nhdsWithin_of_tendsto_nhds (ContinuousAt.tendsto (by fun_prop))

/--
lemma `integral_log_from_zero` / 引理 `integral_log_from_zero`

English:
lemma integral_log_from_zero
  given: {b : Real}
  statement: ∫ s in 0..b, log s = b * log b - b
  proof: by
  rcases lt_trichotomy b 0 with h | h | h
  · -- If t is negative, use that log is an even function to reduce to the positive case.
    conv => arg 1; arg 1; intro t; rw [← log_neg_eq_log]
    rw [intervalIntegral.integral_comp_neg]; rw [intervalIntegral.integral_symm]; rw [neg_zero]; rw [integra

中文:
引理 integral_log_from_zero
  条件: {b : 实数}
  结论: ∫ s in 0..b, log s = b * log b - b
  证明: by
  rcases lt_trichotomy b 0 with h | h | h
  · -- If t is negative, use that log is an even function to reduce to the positive case.
    conv => arg 1; arg 1; intro t; rw [← log_neg_eq_log]
    rw [intervalIntegral.integral_comp_neg]; rw [intervalIntegral.integral_symm]; rw [neg_zero]; rw [integra

Depends on / 依赖: Left.neg_pos_iff.mpr, function, integral_comp_neg, integral_log_from_zero_of_pos, integral_symm, intervalIntegral, intervalIntegral.integral_comp_neg, intervalIntegral.integral_symm, log_neg_eq_log, lt_trichotomy, neg_pos_iff, neg_zero, negative, positive
-/
lemma integral_log_from_zero {b : Real} : ∫ s in 0..b, log s = b * log b - b := by
  rcases lt_trichotomy b 0 with h | h | h
  · -- If t is negative, use that log is an even function to reduce to the positive case.
    conv => arg 1; arg 1; intro t; rw [← log_neg_eq_log]
    rw [intervalIntegral.integral_comp_neg]; rw [intervalIntegral.integral_symm]; rw [neg_zero]; rw [integral_log_from_zero_of_pos (Left.neg_pos_iff.mpr h)]; rw [log_neg_eq_log]
    ring
  · simp [h]
  · exact integral_log_from_zero_of_pos h

@[simp]
/--
theorem `integral_log` / 定理 `integral_log`

English:
theorem integral_log
  statement: ∫ s in a..b, log s = b * log b - a * log a - b + a
  proof: by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)]
  · rw [intervalIntegral.integral_symm, integral_log_from_zero, integral_log_from_zero]
    ring
  all_goals exact intervalIntegrable_log'

@[simp]

中文:
定理 integral_log
  结论: ∫ s in a..b, log s = b * log b - a * log a - b + a
  证明: by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)]
  · rw [intervalIntegral.integral_symm, integral_log_from_zero, integral_log_from_zero]
    ring
  all_goals exact intervalIntegrable_log'

@[simp]

Depends on / 依赖: all_goals, integral_add_adjacent_intervals, integral_log_from_zero, integral_symm, intervalIntegrable_log, intervalIntegral, intervalIntegral.integral_add_adjacent_intervals, intervalIntegral.integral_symm
-/
theorem integral_log : ∫ s in a..b, log s = b * log b - a * log a - b + a := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)]
  · rw [intervalIntegral.integral_symm, integral_log_from_zero, integral_log_from_zero]
    ring
  all_goals exact intervalIntegrable_log'

@[simp]
/--
theorem `integral_sin` / 定理 `integral_sin`

English:
theorem integral_sin
  statement: ∫ x in a..b, sin x = cos a - cos b
  proof: by
  rw [integral_deriv_eq_sub' fun x => -cos x]
  · ring
  · simp
  · simp
  · exact continuousOn_sin

@[simp]

中文:
定理 integral_sin
  结论: ∫ x in a..b, sin x = cos a - cos b
  证明: by
  rw [integral_deriv_eq_sub' fun x => -cos x]
  · ring
  · simp
  · simp
  · exact continuousOn_sin

@[simp]

Depends on / 依赖: continuousOn_sin, integral_deriv_eq_sub
-/
theorem integral_sin : ∫ x in a..b, sin x = cos a - cos b := by
  rw [integral_deriv_eq_sub' fun x => -cos x]
  · ring
  · simp
  · simp
  · exact continuousOn_sin

@[simp]
/--
theorem `integral_cos` / 定理 `integral_cos`

English:
theorem integral_cos
  statement: ∫ x in a..b, cos x = sin b - sin a
  proof: by
  rw [integral_deriv_eq_sub']
  · simp
  · simp only [differentiableAt_sin, implies_true]
  · exact continuousOn_cos

中文:
定理 integral_cos
  结论: ∫ x in a..b, cos x = sin b - sin a
  证明: by
  rw [integral_deriv_eq_sub']
  · simp
  · simp only [differentiableAt_sin, implies_true]
  · exact continuousOn_cos

Depends on / 依赖: continuousOn_cos, differentiableAt_sin, implies_true, integral_deriv_eq_sub
-/
theorem integral_cos : ∫ x in a..b, cos x = sin b - sin a := by
  rw [integral_deriv_eq_sub']
  · simp
  · simp only [differentiableAt_sin, implies_true]
  · exact continuousOn_cos

/--
theorem `integral_cos_mul_complex` / 定理 `integral_cos_mul_complex`

English:
theorem integral_cos_mul_complex
  given: {z : Complex} (hz : z != 0) (a b : Real)
  proof: by
  apply integral_eq_sub_of_hasDerivAt
  swap
· apply Continuous.intervalIntegrable by fun_prop
  intro x _
  have a := Complex.hasDerivAt_sin (↑x * z)
  have b : HasDerivAt (fun y => y * z : Complex -> Complex) z ↑x := hasDerivAt_mul_const _
  have c : HasDerivAt (Complex.sin ∘ fun y : Complex =>

中文:
定理 integral_cos_mul_complex
  条件: {z : 复形} (hz : z != 0) (a b : 实数)
  证明: by
  apply integral_eq_sub_of_hasDerivAt
  swap
· apply Continuous.intervalIntegrable by fun_prop
  intro x _
  have a := Complex.hasDerivAt_sin (↑x * z)
  have b : HasDerivAt (fun y => y * z : Complex -> Complex) z ↑x := hasDerivAt_mul_const _
  have c : HasDerivAt (Complex.sin ∘ fun y : Complex =>

Depends on / 依赖: Complex.hasDerivAt_sin, Complex.sin, Continuous, Continuous.intervalIntegrable, HasDerivAt, HasDerivAt.comp, HasDerivAt.comp_ofReal, c.div_const, comp_ofReal, div_const, fun_prop, hasDerivAt_mul_const, hasDerivAt_sin, integral_eq_sub_of_hasDerivAt, intervalIntegrable
-/
theorem integral_cos_mul_complex {z : Complex} (hz : z != 0) (a b : Real) :
    (∫ x in a..b, Complex.cos (z * x)) = Complex.sin (z * b) / z - Complex.sin (z * a) / z := by
  apply integral_eq_sub_of_hasDerivAt
  swap
· apply Continuous.intervalIntegrable by fun_prop
  intro x _
  have a := Complex.hasDerivAt_sin (↑x * z)
  have b : HasDerivAt (fun y => y * z : Complex -> Complex) z ↑x := hasDerivAt_mul_const _
  have c : HasDerivAt (Complex.sin ∘ fun y : Complex => (y * z)) _ ↑x := HasDerivAt.comp (𝕜 := Complex) x a b
  have d := HasDerivAt.comp_ofReal (c.div_const z)
  grind

/--
theorem `integral_cos_sq_sub_sin_sq` / 定理 `integral_cos_sq_sub_sin_sq`

English:
theorem integral_cos_sq_sub_sin_sq
  proof: by
  simpa only [sq, sub_eq_add_neg, neg_mul_eq_mul_neg] using
    integral_deriv_mul_eq_sub (fun x _ => hasDerivAt_sin x) (fun x _ => hasDerivAt_cos x)
      continuousOn_cos.intervalIntegrable continuousOn_sin.neg.intervalIntegrable

中文:
定理 integral_cos_sq_sub_sin_sq
  证明: by
  simpa only [sq, sub_eq_add_neg, neg_mul_eq_mul_neg] using
    integral_deriv_mul_eq_sub (fun x _ => hasDerivAt_sin x) (fun x _ => hasDerivAt_cos x)
      continuousOn_cos.intervalIntegrable continuousOn_sin.neg.intervalIntegrable

Depends on / 依赖: continuousOn_cos, continuousOn_cos.intervalIntegrable, continuousOn_sin, continuousOn_sin.neg.intervalIntegrable, hasDerivAt_cos, hasDerivAt_sin, integral_deriv_mul_eq_sub, intervalIntegrable, neg_mul_eq_mul_neg, sub_eq_add_neg
-/
theorem integral_cos_sq_sub_sin_sq :
    ∫ x in a..b, cos x ^ 2 - sin x ^ 2 = sin b * cos b - sin a * cos a := by
  simpa only [sq, sub_eq_add_neg, neg_mul_eq_mul_neg] using
    integral_deriv_mul_eq_sub (fun x _ => hasDerivAt_sin x) (fun x _ => hasDerivAt_cos x)
      continuousOn_cos.intervalIntegrable continuousOn_sin.neg.intervalIntegrable

/--
theorem `integral_one_div_one_add_sq` / 定理 `integral_one_div_one_add_sq`

English:
theorem integral_one_div_one_add_sq
  proof: by
  refine integral_deriv_eq_sub' _ Real.deriv_arctan (fun _ _ => differentiableAt_arctan _)
    (continuous_const.div ?_ fun x => ?_).continuousOn
  · fun_prop
  · nlinarith

@[simp]

中文:
定理 integral_one_div_one_add_sq
  证明: by
  refine integral_deriv_eq_sub' _ Real.deriv_arctan (fun _ _ => differentiableAt_arctan _)
    (continuous_const.div ?_ fun x => ?_).continuousOn
  · fun_prop
  · nlinarith

@[simp]

Depends on / 依赖: Real.deriv_arctan, continuousOn, continuous_const, continuous_const.div, deriv_arctan, differentiableAt_arctan, fun_prop, integral_deriv_eq_sub
-/
theorem integral_one_div_one_add_sq :
    (∫ x : Real in a..b, ↑1 / (↑1 + x ^ 2)) = arctan b - arctan a := by
  refine integral_deriv_eq_sub' _ Real.deriv_arctan (fun _ _ => differentiableAt_arctan _)
    (continuous_const.div ?_ fun x => ?_).continuousOn
  · fun_prop
  · nlinarith

@[simp]
/--
theorem `integral_inv_one_add_sq` / 定理 `integral_inv_one_add_sq`

English:
theorem integral_inv_one_add_sq
  statement: (∫ x : Real in a..b, (↑1 + x ^ 2)⁻¹) = arctan b - arctan a
  proof: by
  simp only [← one_div, integral_one_div_one_add_sq]

@[simp]

中文:
定理 integral_inv_one_add_sq
  结论: (∫ x : 实数 in a..b, (↑1 + x ^ 2)⁻¹) = arctan b - arctan a
  证明: by
  simp only [← one_div, integral_one_div_one_add_sq]

@[simp]

Depends on / 依赖: integral_one_div_one_add_sq, one_div
-/
theorem integral_inv_one_add_sq : (∫ x : Real in a..b, (↑1 + x ^ 2)⁻¹) = arctan b - arctan a := by
  simp only [← one_div, integral_one_div_one_add_sq]

@[simp]
/--
theorem `integral_inv_sq_add_sq` / 定理 `integral_inv_sq_add_sq`

English:
theorem integral_inv_sq_add_sq
  given: {c : Real} (hc : c != 0)
  proof: calc
  _ = ∫ x : Real in a..b, (c ^ 2)⁻¹ * (1 + (x / c) ^ 2)⁻¹ := by field_simp
  _ = _ := by
    simp [integral_comp_div (fun x => (c ^ 2)⁻¹ * (1 + x ^ 2)⁻¹) hc]
    field_simp

中文:
定理 integral_inv_sq_add_sq
  条件: {c : 实数} (hc : c != 0)
  证明: calc
  _ = ∫ x : Real in a..b, (c ^ 2)⁻¹ * (1 + (x / c) ^ 2)⁻¹ := by field_simp
  _ = _ := by
    simp [integral_comp_div (fun x => (c ^ 2)⁻¹ * (1 + x ^ 2)⁻¹) hc]
    field_simp
-/
theorem integral_inv_sq_add_sq {c : Real} (hc : c != 0) :
    ∫ x : Real in a..b, (c ^ 2 + x ^ 2)⁻¹ = c⁻¹ * (arctan (b / c) - arctan (a / c)) := calc
  _ = ∫ x : Real in a..b, (c ^ 2)⁻¹ * (1 + (x / c) ^ 2)⁻¹ := by field_simp
  _ = _ := by
    simp [integral_comp_div (fun x => (c ^ 2)⁻¹ * (1 + x ^ 2)⁻¹) hc]
    field_simp

/--
theorem `integral_div_sq_add_sq` / 定理 `integral_div_sq_add_sq`

English:
theorem integral_div_sq_add_sq
  given: {c : Real}
  proof: calc
  _ = ∫ x : Real in a..b, c * (c ^ 2 + x ^ 2)⁻¹ := by ring_nf
  _ = _ := by
    by_cases hc : c = 0
    · simp [hc]
    · rw [integral_const_mul, integral_inv_sq_add_sq hc]
      field_simp

中文:
定理 integral_div_sq_add_sq
  条件: {c : 实数}
  证明: calc
  _ = ∫ x : Real in a..b, c * (c ^ 2 + x ^ 2)⁻¹ := by ring_nf
  _ = _ := by
    by_cases hc : c = 0
    · simp [hc]
    · rw [integral_const_mul, integral_inv_sq_add_sq hc]
      field_simp
-/
theorem integral_div_sq_add_sq {c : Real} :
    ∫ x : Real in a..b, c / (c ^ 2 + x ^ 2) = arctan (b / c) - arctan (a / c) := calc
  _ = ∫ x : Real in a..b, c * (c ^ 2 + x ^ 2)⁻¹ := by ring_nf
  _ = _ := by
    by_cases hc : c = 0
    · simp [hc]
    · rw [integral_const_mul, integral_inv_sq_add_sq hc]
      field_simp

/-- The integrand is chosen to match the conclusion of `Real.deriv_log_log`. -/
@[simp]
/--
theorem `integral_inv_div_log` / 定理 `integral_inv_div_log`

English:
theorem integral_inv_div_log
  given: (ha : 1 < a) (hb : 1 < b)
  proof: by
  rw [← intervalIntegral.integral_congr (fun _ _ => deriv_log_log_apply)]
  refine integral_deriv_eq_sub (fun _ _ => ?_) ?_
  · exact differentiableOn_log_log.differentiableAt (Ioi_mem_nhds (by grind [Set.uIcc]))
.intervalIntegrable refine (?_ : ContinuousOn _ _).congr (fun _ _ => deriv_log_log_a

中文:
定理 integral_inv_div_log
  条件: (ha : 1 < a) (hb : 1 < b)
  证明: by
  rw [← intervalIntegral.integral_congr (fun _ _ => deriv_log_log_apply)]
  refine integral_deriv_eq_sub (fun _ _ => ?_) ?_
  · exact differentiableOn_log_log.differentiableAt (Ioi_mem_nhds (by grind [Set.uIcc]))
.intervalIntegrable refine (?_ : ContinuousOn _ _).congr (fun _ _ => deriv_log_log_a

Depends on / 依赖: ContinuousOn, Ioi_mem_nhds, Set.uIcc, deriv_log_log_apply, differentiableAt, differentiableOn_log_log, differentiableOn_log_log.differentiableAt, fun_prop, integral_congr, integral_deriv_eq_sub, intervalIntegrable, intervalIntegral, intervalIntegral.integral_congr, log_pos
-/
theorem integral_inv_div_log (ha : 1 < a) (hb : 1 < b) :
    ∫ t in a..b, t⁻¹ / log t = log (log b) - log (log a) := by
  rw [← intervalIntegral.integral_congr (fun _ _ => deriv_log_log_apply)]
  refine integral_deriv_eq_sub (fun _ _ => ?_) ?_
  · exact differentiableOn_log_log.differentiableAt (Ioi_mem_nhds (by grind [Set.uIcc]))
.intervalIntegrable refine (?_ : ContinuousOn _ _).congr (fun _ _ => deriv_log_log_apply)
  fun_prop (disch := grind [log_pos, Set.uIcc])

/-- The integrand is chosen to match the conclusion of `Real.deriv_inv_log`. -/
@[simp]
/--
theorem `integral_inv_div_log_sq` / 定理 `integral_inv_div_log_sq`

English:
theorem integral_inv_div_log_sq
  given: (ha : 1 < a) (hb : 1 < b)
  proof: by
  suffices ∫ t in a..b, deriv (fun t => (log t)⁻¹) t = (log b)⁻¹ - (log a)⁻¹ by
    simp_rw [deriv_inv_log, neg_div, intervalIntegral.integral_neg] at this
    linarith
  refine integral_deriv_eq_sub (fun _ _ => ?_) (ContinuousOn.intervalIntegrable ?_)
  · exact differentiableOn_inv_log.different

中文:
定理 integral_inv_div_log_sq
  条件: (ha : 1 < a) (hb : 1 < b)
  证明: by
  suffices ∫ t in a..b, deriv (fun t => (log t)⁻¹) t = (log b)⁻¹ - (log a)⁻¹ by
    simp_rw [deriv_inv_log, neg_div, intervalIntegral.integral_neg] at this
    linarith
  refine integral_deriv_eq_sub (fun _ _ => ?_) (ContinuousOn.intervalIntegrable ?_)
  · exact differentiableOn_inv_log.different

Depends on / 依赖: ContinuousOn, ContinuousOn.intervalIntegrable, Ioi_mem_nhds, Set.uIcc, convert, deriv_inv_log, differentiableAt, differentiableOn_inv_log, differentiableOn_inv_log.differentiableAt, fun_prop, integral_deriv_eq_sub, integral_neg, intervalIntegrable, intervalIntegral, intervalIntegral.integral_neg, log_pos, neg_div, simp_rw
-/
theorem integral_inv_div_log_sq (ha : 1 < a) (hb : 1 < b) :
    ∫ t in a..b, t⁻¹ / log t ^ 2 = (log a)⁻¹ - (log b)⁻¹ := by
  suffices ∫ t in a..b, deriv (fun t => (log t)⁻¹) t = (log b)⁻¹ - (log a)⁻¹ by
    simp_rw [deriv_inv_log, neg_div, intervalIntegral.integral_neg] at this
    linarith
  refine integral_deriv_eq_sub (fun _ _ => ?_) (ContinuousOn.intervalIntegrable ?_)
  · exact differentiableOn_inv_log.differentiableAt (Ioi_mem_nhds (by grind [Set.uIcc]))
  suffices ContinuousOn (fun x => (-x⁻¹) * ((log x)⁻¹) ^ 2) (.uIcc a b) by
    convert this using 2 with x
    simp [field]
  fun_prop (disch := grind [log_pos, Set.uIcc])

section RpowCpow

open Complex

/--
theorem `integral_mul_cpow_one_add_sq` / 定理 `integral_mul_cpow_one_add_sq`

English:
theorem integral_mul_cpow_one_add_sq
  given: {t : Complex} (ht : t != -1)
  proof: by
  have : t + 1 != 0 := by contrapose ht; rwa [add_eq_zero_iff_eq_neg] at ht
  apply integral_eq_sub_of_hasDerivAt
  · intro x _
    have f : HasDerivAt (fun y : Complex => 1 + y ^ 2) (2 * x : Complex) x := by
      convert! (hasDerivAt_pow 2 (x : Complex)).const_add 1
      simp
    have g :
    

中文:
定理 integral_mul_cpow_one_add_sq
  条件: {t : 复形} (ht : t != -1)
  证明: by
  have : t + 1 != 0 := by contrapose ht; rwa [add_eq_zero_iff_eq_neg] at ht
  apply integral_eq_sub_of_hasDerivAt
  · intro x _
    have f : HasDerivAt (fun y : Complex => 1 + y ^ 2) (2 * x : Complex) x := by
      convert! (hasDerivAt_pow 2 (x : Complex)).const_add 1
      simp
    have g :
    

Depends on / 依赖: HasDerivAt, HasDerivAt.cpow_const, Or.inl, add_eq_zero_iff_eq_neg, const_add, contrapose, convert, cpow_const, div_const, hasDerivAt_id, hasDerivAt_pow, integral_eq_sub_of_hasDerivAt, z.re
-/
theorem integral_mul_cpow_one_add_sq {t : Complex} (ht : t != -1) :
    (∫ x : Real in a..b, (x : Complex) * ((1 : Complex) + ↑x ^ 2) ^ t) =
      ((1 : Complex) + (b : Complex) ^ 2) ^ (t + 1) / (2 * (t + ↑1)) -
      ((1 : Complex) + (a : Complex) ^ 2) ^ (t + 1) / (2 * (t + ↑1)) := by
  have : t + 1 != 0 := by contrapose ht; rwa [add_eq_zero_iff_eq_neg] at ht
  apply integral_eq_sub_of_hasDerivAt
  · intro x _
    have f : HasDerivAt (fun y : Complex => 1 + y ^ 2) (2 * x : Complex) x := by
      convert! (hasDerivAt_pow 2 (x : Complex)).const_add 1
      simp
    have g :
      forall {z : Complex}, 0 < z.re -> HasDerivAt (fun z => z ^ (t + 1) / (2 * (t + 1))) (z ^ t / 2) z := by
      intro z hz
      convert!
        (HasDerivAt.cpow_const (c := t + 1) (hasDerivAt_id _) (Or.inl hz)).div_const
          (2 * (t + 1)) using 1
      simp [field]
    convert! (HasDerivAt.comp (↑x) (g _) f).comp_ofReal using 1
    · ring
    · exact mod_cast add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg x)
  · apply Continuous.intervalIntegrable
    refine continuous_ofReal.mul ?_
    apply Continuous.cpow (by fun_prop) continuous_const
    intro a
    norm_cast
exact ofReal_mem_slitPlane.2 add_pos_of_pos_of_nonneg one_pos sq_nonneg a

/--
theorem `integral_mul_rpow_one_add_sq` / 定理 `integral_mul_rpow_one_add_sq`

English:
theorem integral_mul_rpow_one_add_sq
  given: {t : Real} (ht : t != -1)
  proof: by
  have : forall x s : Real, (((↑1 + x ^ 2) ^ s : Real) : Complex) = (1 + (x : Complex) ^ 2) ^ (s : Complex) := by
    intro x s
    norm_cast
    rw [ofReal_cpow]; rw [ofReal_add]; rw [ofReal_pow]; rw [ofReal_one]
    exact add_nonneg zero_le_one (sq_nonneg x)
  rw [← ofReal_inj]
  convert! integ

中文:
定理 integral_mul_rpow_one_add_sq
  条件: {t : 实数} (ht : t != -1)
  证明: by
  have : forall x s : Real, (((↑1 + x ^ 2) ^ s : Real) : Complex) = (1 + (x : Complex) ^ 2) ^ (s : Complex) := by
    intro x s
    norm_cast
    rw [ofReal_cpow]; rw [ofReal_add]; rw [ofReal_pow]; rw [ofReal_one]
    exact add_nonneg zero_le_one (sq_nonneg x)
  rw [← ofReal_inj]
  convert! integ

Depends on / 依赖: add_nonneg, convert, integral_mul_cpow_one_add_sq, integral_ofReal, intervalIntegral, intervalIntegral.integral_ofReal, ofReal_add, ofReal_cpow, ofReal_div, ofReal_inj, ofReal_mul, ofReal_one, ofReal_pow, ofReal_sub, simp_rw, sq_nonneg, zero_le_one
-/
theorem integral_mul_rpow_one_add_sq {t : Real} (ht : t != -1) :
    (∫ x : Real in a..b, x * (↑1 + x ^ 2) ^ t) =
      (↑1 + b ^ 2) ^ (t + 1) / (↑2 * (t + ↑1)) - (↑1 + a ^ 2) ^ (t + 1) / (↑2 * (t + ↑1)) := by
  have : forall x s : Real, (((↑1 + x ^ 2) ^ s : Real) : Complex) = (1 + (x : Complex) ^ 2) ^ (s : Complex) := by
    intro x s
    norm_cast
    rw [ofReal_cpow]; rw [ofReal_add]; rw [ofReal_pow]; rw [ofReal_one]
    exact add_nonneg zero_le_one (sq_nonneg x)
  rw [← ofReal_inj]
  convert! integral_mul_cpow_one_add_sq (_ : (t : Complex) != -1)
  · rw [← intervalIntegral.integral_ofReal]
    congr with x : 1
    rw [ofReal_mul]; rw [this x t]
  · simp_rw [ofReal_sub, ofReal_div, this a (t + 1), this b (t + 1)]
    push_cast; rfl
  · rw [← ofReal_one, ← ofReal_neg, Ne, ofReal_inj]
    exact ht

end RpowCpow

open Nat


/--
theorem `integral_sin_pow_aux` / 定理 `integral_sin_pow_aux`

English:
theorem integral_sin_pow_aux
  proof: by
  let C := sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b
  have h : forall α β γ : Real, β * α * γ * α = β * (α * α * γ) := fun α β γ => by ring
  have hu : forall x in [[a, b]],
      HasDerivAt (fun y => sin y ^ (n + 1)) ((n + 1 : Nat) * cos x * sin x ^ n) x :=
    fun x _ => by simpa only 

中文:
定理 integral_sin_pow_aux
  证明: by
  let C := sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b
  have h : forall α β γ : Real, β * α * γ * α = β * (α * α * γ) := fun α β γ => by ring
  have hu : forall x in [[a, b]],
      HasDerivAt (fun y => sin y ^ (n + 1)) ((n + 1 : Nat) * cos x * sin x ^ n) x :=
    fun x _ => by simpa only 

Depends on / 依赖: HasDerivAt, hasDerivAt_cos, hasDerivAt_sin, integral_mul_deriv_eq_d, mul_right_comm, neg_neg
-/
theorem integral_sin_pow_aux :
    (∫ x in a..b, sin x ^ (n + 2)) =
      (sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b + (↑n + 1) * ∫ x in a..b, sin x ^ n) -
        (↑n + 1) * ∫ x in a..b, sin x ^ (n + 2) := by
  let C := sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b
  have h : forall α β γ : Real, β * α * γ * α = β * (α * α * γ) := fun α β γ => by ring
  have hu : forall x in [[a, b]],
      HasDerivAt (fun y => sin y ^ (n + 1)) ((n + 1 : Nat) * cos x * sin x ^ n) x :=
    fun x _ => by simpa only [mul_right_comm] using! (hasDerivAt_sin x).pow (n + 1)
  have hv : forall x in [[a, b]], HasDerivAt (-cos) (sin x) x := fun x _ => by
    simpa only [neg_neg] using! (hasDerivAt_cos x).neg
  have H := integral_mul_deriv_eq_deriv_mul hu hv ?_ ?_
  · calc
      (∫ x in a..b, sin x ^ (n + 2)) = ∫ x in a..b, sin x ^ (n + 1) * sin x := by
        simp only [_root_.pow_succ]
      _ = C + (↑n + 1) * ∫ x in a..b, cos x ^ 2 * sin x ^ n := by simp [H, h, sq]; ring
      _ = C + (↑n + 1) * ∫ x in a..b, sin x ^ n - sin x ^ (n + 2) := by
        simp [cos_sq', sub_mul, ← pow_add, add_comm]
      _ = (C + (↑n + 1) * ∫ x in a..b, sin x ^ n) - (↑n + 1) * ∫ x in a..b, sin x ^ (n + 2) := by
        rw [integral_sub]; rw [mul_sub]; rw [add_sub_assoc] <;>
          apply Continuous.intervalIntegrable <;> fun_prop
  all_goals apply Continuous.intervalIntegrable; fun_prop

/--
theorem `integral_sin_pow` / 定理 `integral_sin_pow`

English:
theorem integral_sin_pow
  proof: by
  field_simp
  convert! eq_sub_iff_add_eq.mp (integral_sin_pow_aux n) using 1
  ring

@[simp]

中文:
定理 integral_sin_pow
  证明: by
  field_simp
  convert! eq_sub_iff_add_eq.mp (integral_sin_pow_aux n) using 1
  ring

@[simp]

Depends on / 依赖: convert, eq_sub_iff_add_eq, eq_sub_iff_add_eq.mp, integral_sin_pow_aux
-/
theorem integral_sin_pow :
    (∫ x in a..b, sin x ^ (n + 2)) =
      (sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b) / (n + 2) +
        (n + 1) / (n + 2) * ∫ x in a..b, sin x ^ n := by
  field_simp
  convert! eq_sub_iff_add_eq.mp (integral_sin_pow_aux n) using 1
  ring

@[simp]
/--
theorem `integral_sin_sq` / 定理 `integral_sin_sq`

English:
theorem integral_sin_sq
  statement: ∫ x in a..b, sin x ^ 2 = (sin a * cos a - sin b * cos b + b - a) / 2
  proof: by
  simp [field, integral_sin_pow, add_sub_assoc]

中文:
定理 integral_sin_sq
  结论: ∫ x in a..b, sin x ^ 2 = (sin a * cos a - sin b * cos b + b - a) / 2
  证明: by
  simp [field, integral_sin_pow, add_sub_assoc]

Depends on / 依赖: add_sub_assoc, integral_sin_pow
-/
theorem integral_sin_sq : ∫ x in a..b, sin x ^ 2 = (sin a * cos a - sin b * cos b + b - a) / 2 := by
  simp [field, integral_sin_pow, add_sub_assoc]

/--
theorem `integral_sin_pow_odd` / 定理 `integral_sin_pow_odd`

English:
theorem integral_sin_pow_odd
  proof: by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rw [prod_range_succ_comm]; rw [mul_left_comm]; rw [← ih]; rw [mul_succ]; rw [integral_sin_pow]
    norm_cast
    field_simp
    simp

中文:
定理 integral_sin_pow_odd
  证明: by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rw [prod_range_succ_comm]; rw [mul_left_comm]; rw [← ih]; rw [mul_succ]; rw [integral_sin_pow]
    norm_cast
    field_simp
    simp

Depends on / 依赖: integral_sin_pow, mul_left_comm, mul_succ, prod_range_succ_comm
-/
theorem integral_sin_pow_odd :
    (∫ x in 0..π, sin x ^ (2 * n + 1)) = 2 * ∏ i in range n, (2 * (i : Real) + 2) / (2 * i + 3) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rw [prod_range_succ_comm]; rw [mul_left_comm]; rw [← ih]; rw [mul_succ]; rw [integral_sin_pow]
    norm_cast
    field_simp
    simp

/--
theorem `integral_sin_pow_even` / 定理 `integral_sin_pow_even`

English:
theorem integral_sin_pow_even
  proof: by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ_comm]; rw [mul_left_comm]; rw [← ih]; rw [mul_succ]; rw [integral_sin_pow]
    norm_cast
    field_simp
    simp

中文:
定理 integral_sin_pow_even
  证明: by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ_comm]; rw [mul_left_comm]; rw [← ih]; rw [mul_succ]; rw [integral_sin_pow]
    norm_cast
    field_simp
    simp

Depends on / 依赖: integral_sin_pow, mul_left_comm, mul_succ, prod_range_succ_comm
-/
theorem integral_sin_pow_even :
    (∫ x in 0..π, sin x ^ (2 * n)) = π * ∏ i in range n, (2 * (i : Real) + 1) / (2 * i + 2) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ_comm]; rw [mul_left_comm]; rw [← ih]; rw [mul_succ]; rw [integral_sin_pow]
    norm_cast
    field_simp
    simp

/--
theorem `integral_sin_pow_pos` / 定理 `integral_sin_pow_pos`

English:
theorem integral_sin_pow_pos
  statement: 0 < ∫ x in 0..π, sin x ^ n
  proof: by
  rcases even_or_odd' n with ⟨k, rfl | rfl⟩ <;>
  simp only [integral_sin_pow_even, integral_sin_pow_odd] <;>
  refine mul_pos (by simp [pi_pos]) (prod_pos fun n _ => div_pos ?_ ?_) <;>
  norm_cast <;>
  lia

中文:
定理 integral_sin_pow_pos
  结论: 0 < ∫ x in 0..π, sin x ^ n
  证明: by
  rcases even_or_odd' n with ⟨k, rfl | rfl⟩ <;>
  simp only [integral_sin_pow_even, integral_sin_pow_odd] <;>
  refine mul_pos (by simp [pi_pos]) (prod_pos fun n _ => div_pos ?_ ?_) <;>
  norm_cast <;>
  lia

Depends on / 依赖: div_pos, even_or_odd, integral_sin_pow_even, integral_sin_pow_odd, mul_pos, pi_pos, prod_pos
-/
theorem integral_sin_pow_pos : 0 < ∫ x in 0..π, sin x ^ n := by
  rcases even_or_odd' n with ⟨k, rfl | rfl⟩ <;>
  simp only [integral_sin_pow_even, integral_sin_pow_odd] <;>
  refine mul_pos (by simp [pi_pos]) (prod_pos fun n _ => div_pos ?_ ?_) <;>
  norm_cast <;>
  lia

/--
theorem `integral_sin_pow_succ_le` / 定理 `integral_sin_pow_succ_le`

English:
theorem integral_sin_pow_succ_le
  statement: (∫ x in 0..π, sin x ^ (n + 1)) <= ∫ x in 0..π, sin x ^ n
  proof: by
  let H x h := pow_le_pow_of_le_one (sin_nonneg_of_mem_Icc h) (sin_le_one x) (n.le_add_right 1)
  refine integral_mono_on pi_pos.le ?_ ?_ H <;> exact (continuous_sin.pow _).intervalIntegrable 0 π

中文:
定理 integral_sin_pow_succ_le
  结论: (∫ x in 0..π, sin x ^ (n + 1)) <= ∫ x in 0..π, sin x ^ n
  证明: by
  let H x h := pow_le_pow_of_le_one (sin_nonneg_of_mem_Icc h) (sin_le_one x) (n.le_add_right 1)
  refine integral_mono_on pi_pos.le ?_ ?_ H <;> exact (continuous_sin.pow _).intervalIntegrable 0 π

Depends on / 依赖: continuous_sin, continuous_sin.pow, integral_mono_on, intervalIntegrable, le_add_right, n.le_add_right, pi_pos, pi_pos.le, pow_le_pow_of_le_one, sin_le_one, sin_nonneg_of_mem_Icc
-/
theorem integral_sin_pow_succ_le : (∫ x in 0..π, sin x ^ (n + 1)) <= ∫ x in 0..π, sin x ^ n := by
  let H x h := pow_le_pow_of_le_one (sin_nonneg_of_mem_Icc h) (sin_le_one x) (n.le_add_right 1)
  refine integral_mono_on pi_pos.le ?_ ?_ H <;> exact (continuous_sin.pow _).intervalIntegrable 0 π

/--
theorem `integral_sin_pow_antitone` / 定理 `integral_sin_pow_antitone`

English:
theorem integral_sin_pow_antitone
  statement: Antitone fun n : Nat => ∫ x in 0..π, sin x ^ n
  proof: antitone_nat_of_succ_le integral_sin_pow_succ_le

中文:
定理 integral_sin_pow_antitone
  结论: 递减 fun n : 自然数 => ∫ x in 0..π, sin x ^ n
  证明: antitone_nat_of_succ_le integral_sin_pow_succ_le

Depends on / 依赖: antitone_nat_of_succ_le, integral_sin_pow_succ_le
-/
theorem integral_sin_pow_antitone : Antitone fun n : Nat => ∫ x in 0..π, sin x ^ n :=
  antitone_nat_of_succ_le integral_sin_pow_succ_le



/--
theorem `integral_cos_pow_aux` / 定理 `integral_cos_pow_aux`

English:
theorem integral_cos_pow_aux
  proof: by
  let C := cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a
  have h : forall α β γ : Real, β * α * γ * α = β * (α * α * γ) := fun α β γ => by ring
  have hu : forall x in [[a, b]],
      HasDerivAt (fun y => cos y ^ (n + 1)) (-(n + 1 : Nat) * sin x * cos x ^ n) x :=
    fun x _ => by
      simp

中文:
定理 integral_cos_pow_aux
  证明: by
  let C := cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a
  have h : forall α β γ : Real, β * α * γ * α = β * (α * α * γ) := fun α β γ => by ring
  have hu : forall x in [[a, b]],
      HasDerivAt (fun y => cos y ^ (n + 1)) (-(n + 1 : Nat) * sin x * cos x ^ n) x :=
    fun x _ => by
      simp

Depends on / 依赖: HasDerivAt, hasDerivAt_cos, hasDerivAt_sin, integral_mul_deriv_eq_deriv_mul, mul_neg, mul_right_comm, neg_mul
-/
theorem integral_cos_pow_aux :
    (∫ x in a..b, cos x ^ (n + 2)) =
      (cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a + (n + 1) * ∫ x in a..b, cos x ^ n) -
        (n + 1) * ∫ x in a..b, cos x ^ (n + 2) := by
  let C := cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a
  have h : forall α β γ : Real, β * α * γ * α = β * (α * α * γ) := fun α β γ => by ring
  have hu : forall x in [[a, b]],
      HasDerivAt (fun y => cos y ^ (n + 1)) (-(n + 1 : Nat) * sin x * cos x ^ n) x :=
    fun x _ => by
      simpa only [mul_right_comm, neg_mul, mul_neg] using! (hasDerivAt_cos x).pow (n + 1)
  have hv : forall x in [[a, b]], HasDerivAt sin (cos x) x := fun x _ => hasDerivAt_sin x
  have H := integral_mul_deriv_eq_deriv_mul hu hv ?_ ?_
  · calc
      (∫ x in a..b, cos x ^ (n + 2)) = ∫ x in a..b, cos x ^ (n + 1) * cos x := by
        simp only [_root_.pow_succ]
      _ = C + (n + 1) * ∫ x in a..b, sin x ^ 2 * cos x ^ n := by simp [C, H, h, sq, -neg_add_rev]
      _ = C + (n + 1) * ∫ x in a..b, cos x ^ n - cos x ^ (n + 2) := by
        simp [sin_sq, sub_mul, ← pow_add, add_comm]
      _ = (C + (n + 1) * ∫ x in a..b, cos x ^ n) - (n + 1) * ∫ x in a..b, cos x ^ (n + 2) := by
        rw [integral_sub]; rw [mul_sub]; rw [add_sub_assoc] <;>
          apply Continuous.intervalIntegrable <;> fun_prop
  all_goals apply Continuous.intervalIntegrable; fun_prop

/--
theorem `integral_cos_pow` / 定理 `integral_cos_pow`

English:
theorem integral_cos_pow
  proof: by
  field_simp
  convert! eq_sub_iff_add_eq.mp (integral_cos_pow_aux n) using 1
  ring

@[simp]

中文:
定理 integral_cos_pow
  证明: by
  field_simp
  convert! eq_sub_iff_add_eq.mp (integral_cos_pow_aux n) using 1
  ring

@[simp]

Depends on / 依赖: convert, eq_sub_iff_add_eq, eq_sub_iff_add_eq.mp, integral_cos_pow_aux
-/
theorem integral_cos_pow :
    (∫ x in a..b, cos x ^ (n + 2)) =
      (cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a) / (n + 2) +
        (n + 1) / (n + 2) * ∫ x in a..b, cos x ^ n := by
  field_simp
  convert! eq_sub_iff_add_eq.mp (integral_cos_pow_aux n) using 1
  ring

@[simp]
/--
theorem `integral_cos_sq` / 定理 `integral_cos_sq`

English:
theorem integral_cos_sq
  statement: ∫ x in a..b, cos x ^ 2 = (cos b * sin b - cos a * sin a + b - a) / 2
  proof: by
  simp [field, integral_cos_pow, add_sub_assoc]

中文:
定理 integral_cos_sq
  结论: ∫ x in a..b, cos x ^ 2 = (cos b * sin b - cos a * sin a + b - a) / 2
  证明: by
  simp [field, integral_cos_pow, add_sub_assoc]

Depends on / 依赖: add_sub_assoc, integral_cos_pow
-/
theorem integral_cos_sq : ∫ x in a..b, cos x ^ 2 = (cos b * sin b - cos a * sin a + b - a) / 2 := by
  simp [field, integral_cos_pow, add_sub_assoc]

/-! ### Integral of `sin x ^ m * cos x ^ n` -/


/--
theorem `integral_sin_pow_mul_cos_pow_odd` / 定理 `integral_sin_pow_mul_cos_pow_odd`

English:
theorem integral_sin_pow_mul_cos_pow_odd
  given: (m n : Nat)
  proof: have hc : Continuous fun u : Real => u ^ m * (↑1 - u ^ 2) ^ n := by fun_prop
  calc
    (∫ x in a..b, sin x ^ m * cos x ^ (2 * n + 1)) =
        ∫ x in a..b, sin x ^ m * (↑1 - sin x ^ 2) ^ n * cos x := by
      simp only [_root_.pow_zero, _root_.pow_succ, mul_assoc, pow_mul, one_mul]
      congr! 5


中文:
定理 integral_sin_pow_mul_cos_pow_odd
  条件: (m n : 自然数)
  证明: have hc : Continuous fun u : Real => u ^ m * (↑1 - u ^ 2) ^ n := by fun_prop
  calc
    (∫ x in a..b, sin x ^ m * cos x ^ (2 * n + 1)) =
        ∫ x in a..b, sin x ^ m * (↑1 - sin x ^ 2) ^ n * cos x := by
      simp only [_root_.pow_zero, _root_.pow_succ, mul_assoc, pow_mul, one_mul]
      congr! 5


Depends on / 依赖: Continuous, _root_, _root_.pow_succ, _root_.pow_zero, continuousOn_cos, cos_sq, fun_prop, hasDerivAt_sin, integral_comp_mul_deriv, mul_assoc, one_mul, pow_mul, pow_succ, pow_zero
-/
theorem integral_sin_pow_mul_cos_pow_odd (m n : Nat) :
    (∫ x in a..b, sin x ^ m * cos x ^ (2 * n + 1)) = ∫ u in sin a..sin b, u ^ m * (1 - u ^ 2) ^ n :=
  have hc : Continuous fun u : Real => u ^ m * (↑1 - u ^ 2) ^ n := by fun_prop
  calc
    (∫ x in a..b, sin x ^ m * cos x ^ (2 * n + 1)) =
        ∫ x in a..b, sin x ^ m * (↑1 - sin x ^ 2) ^ n * cos x := by
      simp only [_root_.pow_zero, _root_.pow_succ, mul_assoc, pow_mul, one_mul]
      congr! 5
      rw [← sq]; rw [← sq]; rw [cos_sq']
    _ = ∫ u in sin a..sin b, u ^ m * (1 - u ^ 2) ^ n :=
      integral_comp_mul_deriv (fun x _ => hasDerivAt_sin x) continuousOn_cos hc

/-- The integral of `sin x * cos x`, given in terms of sin².
  See `integral_sin_mul_cos₂` below for the integral given in terms of cos². -/
@[simp]
/--
theorem `integral_sin_mul_cos₁` / 定理 `integral_sin_mul_cos₁`

English:
theorem integral_sin_mul_cos₁
  statement: ∫ x in a..b, sin x * cos x = (sin b ^ 2 - sin a ^ 2) / 2
  proof: by
  simpa using integral_sin_pow_mul_cos_pow_odd 1 0

@[simp]

中文:
定理 integral_sin_mul_cos₁
  结论: ∫ x in a..b, sin x * cos x = (sin b ^ 2 - sin a ^ 2) / 2
  证明: by
  simpa using integral_sin_pow_mul_cos_pow_odd 1 0

@[simp]

Depends on / 依赖: integral_sin_pow_mul_cos_pow_odd
-/
theorem integral_sin_mul_cos₁ : ∫ x in a..b, sin x * cos x = (sin b ^ 2 - sin a ^ 2) / 2 := by
  simpa using integral_sin_pow_mul_cos_pow_odd 1 0

@[simp]
/--
theorem `integral_sin_sq_mul_cos` / 定理 `integral_sin_sq_mul_cos`

English:
theorem integral_sin_sq_mul_cos
  proof: by
  have := @integral_sin_pow_mul_cos_pow_odd a b 2 0
  norm_num at this; exact this

@[simp]

中文:
定理 integral_sin_sq_mul_cos
  证明: by
  have := @integral_sin_pow_mul_cos_pow_odd a b 2 0
  norm_num at this; exact this

@[simp]

Depends on / 依赖: integral_sin_pow_mul_cos_pow_odd
-/
theorem integral_sin_sq_mul_cos :
    ∫ x in a..b, sin x ^ 2 * cos x = (sin b ^ 3 - sin a ^ 3) / 3 := by
  have := @integral_sin_pow_mul_cos_pow_odd a b 2 0
  norm_num at this; exact this

@[simp]
/--
theorem `integral_cos_pow_three` / 定理 `integral_cos_pow_three`

English:
theorem integral_cos_pow_three
  proof: by
  have := @integral_sin_pow_mul_cos_pow_odd a b 0 1
  norm_num at this; exact this

中文:
定理 integral_cos_pow_three
  证明: by
  have := @integral_sin_pow_mul_cos_pow_odd a b 0 1
  norm_num at this; exact this

Depends on / 依赖: integral_sin_pow_mul_cos_pow_odd
-/
theorem integral_cos_pow_three :
    ∫ x in a..b, cos x ^ 3 = sin b - sin a - (sin b ^ 3 - sin a ^ 3) / 3 := by
  have := @integral_sin_pow_mul_cos_pow_odd a b 0 1
  norm_num at this; exact this

/--
theorem `integral_sin_pow_odd_mul_cos_pow` / 定理 `integral_sin_pow_odd_mul_cos_pow`

English:
theorem integral_sin_pow_odd_mul_cos_pow
  given: (m n : Nat)
  proof: have hc : Continuous fun u : Real => u ^ n * (↑1 - u ^ 2) ^ m := by fun_prop
  calc
    (∫ x in a..b, sin x ^ (2 * m + 1) * cos x ^ n) =
        -∫ x in b..a, sin x ^ (2 * m + 1) * cos x ^ n := by rw [integral_symm]
    _ = ∫ x in b..a, (↑1 - cos x ^ 2) ^ m * -sin x * cos x ^ n := by
      simp only

中文:
定理 integral_sin_pow_odd_mul_cos_pow
  条件: (m n : 自然数)
  证明: have hc : Continuous fun u : Real => u ^ n * (↑1 - u ^ 2) ^ m := by fun_prop
  calc
    (∫ x in a..b, sin x ^ (2 * m + 1) * cos x ^ n) =
        -∫ x in b..a, sin x ^ (2 * m + 1) * cos x ^ n := by rw [integral_symm]
    _ = ∫ x in b..a, (↑1 - cos x ^ 2) ^ m * -sin x * cos x ^ n := by
      simp only

Depends on / 依赖: Continuous, _root_, _root_.pow_succ, _root_.pow_zero, fun_prop, integral_neg, integral_symm, mul_neg, neg_inj, neg_mul, one_mul, pow_mul, pow_succ, pow_zero, sin_sq
-/
theorem integral_sin_pow_odd_mul_cos_pow (m n : Nat) :
    (∫ x in a..b, sin x ^ (2 * m + 1) * cos x ^ n) = ∫ u in cos b..cos a, u ^ n * (1 - u ^ 2) ^ m :=
  have hc : Continuous fun u : Real => u ^ n * (↑1 - u ^ 2) ^ m := by fun_prop
  calc
    (∫ x in a..b, sin x ^ (2 * m + 1) * cos x ^ n) =
        -∫ x in b..a, sin x ^ (2 * m + 1) * cos x ^ n := by rw [integral_symm]
    _ = ∫ x in b..a, (↑1 - cos x ^ 2) ^ m * -sin x * cos x ^ n := by
      simp only [_root_.pow_succ, pow_mul, _root_.pow_zero, one_mul, mul_neg, neg_mul,
        integral_neg, neg_inj]
      congr! 5
      rw [← sq]; rw [← sq]; rw [sin_sq]
    _ = ∫ x in b..a, cos x ^ n * (↑1 - cos x ^ 2) ^ m * -sin x := by congr; ext; ring
    _ = ∫ u in cos b..cos a, u ^ n * (↑1 - u ^ 2) ^ m :=
      integral_comp_mul_deriv (fun x _ => hasDerivAt_cos x) continuousOn_sin.neg hc

/--
theorem `integral_sin_mul_cos₂` / 定理 `integral_sin_mul_cos₂`

English:
theorem integral_sin_mul_cos₂
  statement: ∫ x in a..b, sin x * cos x = (cos a ^ 2 - cos b ^ 2) / 2
  proof: by
  simpa using integral_sin_pow_odd_mul_cos_pow 0 1

@[simp]

中文:
定理 integral_sin_mul_cos₂
  结论: ∫ x in a..b, sin x * cos x = (cos a ^ 2 - cos b ^ 2) / 2
  证明: by
  simpa using integral_sin_pow_odd_mul_cos_pow 0 1

@[simp]

Depends on / 依赖: integral_sin_pow_odd_mul_cos_pow
-/
theorem integral_sin_mul_cos₂ : ∫ x in a..b, sin x * cos x = (cos a ^ 2 - cos b ^ 2) / 2 := by
  simpa using integral_sin_pow_odd_mul_cos_pow 0 1

@[simp]
/--
theorem `integral_sin_mul_cos_sq` / 定理 `integral_sin_mul_cos_sq`

English:
theorem integral_sin_mul_cos_sq
  proof: by
  have := @integral_sin_pow_odd_mul_cos_pow a b 0 2
  norm_num at this; exact this

@[simp]

中文:
定理 integral_sin_mul_cos_sq
  证明: by
  have := @integral_sin_pow_odd_mul_cos_pow a b 0 2
  norm_num at this; exact this

@[simp]

Depends on / 依赖: integral_sin_pow_odd_mul_cos_pow
-/
theorem integral_sin_mul_cos_sq :
    ∫ x in a..b, sin x * cos x ^ 2 = (cos a ^ 3 - cos b ^ 3) / 3 := by
  have := @integral_sin_pow_odd_mul_cos_pow a b 0 2
  norm_num at this; exact this

@[simp]
/--
theorem `integral_sin_pow_three` / 定理 `integral_sin_pow_three`

English:
theorem integral_sin_pow_three
  proof: by
  have := @integral_sin_pow_odd_mul_cos_pow a b 1 0
  norm_num at this; exact this

中文:
定理 integral_sin_pow_three
  证明: by
  have := @integral_sin_pow_odd_mul_cos_pow a b 1 0
  norm_num at this; exact this

Depends on / 依赖: integral_sin_pow_odd_mul_cos_pow
-/
theorem integral_sin_pow_three :
    ∫ x in a..b, sin x ^ 3 = cos a - cos b - (cos a ^ 3 - cos b ^ 3) / 3 := by
  have := @integral_sin_pow_odd_mul_cos_pow a b 1 0
  norm_num at this; exact this

/--
theorem `integral_sin_pow_even_mul_cos_pow_even` / 定理 `integral_sin_pow_even_mul_cos_pow_even`

English:
theorem integral_sin_pow_even_mul_cos_pow_even
  given: (m n : Nat)
  proof: by
  simp [pow_mul, sin_sq, cos_sq, ← sub_sub]
  field_simp
  norm_num

@[simp]

中文:
定理 integral_sin_pow_even_mul_cos_pow_even
  条件: (m n : 自然数)
  证明: by
  simp [pow_mul, sin_sq, cos_sq, ← sub_sub]
  field_simp
  norm_num

@[simp]

Depends on / 依赖: cos_sq, pow_mul, sin_sq, sub_sub
-/
theorem integral_sin_pow_even_mul_cos_pow_even (m n : Nat) :
    (∫ x in a..b, sin x ^ (2 * m) * cos x ^ (2 * n)) =
      ∫ x in a..b, ((1 - cos (2 * x)) / 2) ^ m * ((1 + cos (2 * x)) / 2) ^ n := by
  simp [pow_mul, sin_sq, cos_sq, ← sub_sub]
  field_simp
  norm_num

@[simp]
/--
theorem `integral_sin_sq_mul_cos_sq` / 定理 `integral_sin_sq_mul_cos_sq`

English:
theorem integral_sin_sq_mul_cos_sq
  proof: by
  convert! integral_sin_pow_even_mul_cos_pow_even 1 1 using 1
  have h1 : forall c : Real, (↑1 - c) / ↑2 * ((↑1 + c) / ↑2) = (↑1 - c ^ 2) / 4 := fun c => by ring
  have h2 : Continuous fun x => cos (2 * x) ^ 2 := by fun_prop
  have h3 : forall x, cos x * sin x = sin (2 * x) / 2 := by intro; rw [s

中文:
定理 integral_sin_sq_mul_cos_sq
  证明: by
  convert! integral_sin_pow_even_mul_cos_pow_even 1 1 using 1
  have h1 : forall c : Real, (↑1 - c) / ↑2 * ((↑1 + c) / ↑2) = (↑1 - c ^ 2) / 4 := fun c => by ring
  have h2 : Continuous fun x => cos (2 * x) ^ 2 := by fun_prop
  have h3 : forall x, cos x * sin x = sin (2 * x) / 2 := by intro; rw [s

Depends on / 依赖: Continuous, convert, fun_prop, h2.intervalIntegrable, integral_comp_mul_left, integral_sin_pow_even_mul_cos_pow_even, intervalIntegrable, sin_two_mul
-/
theorem integral_sin_sq_mul_cos_sq :
    ∫ x in a..b, sin x ^ 2 * cos x ^ 2 = (b - a) / 8 - (sin (4 * b) - sin (4 * a)) / 32 := by
  convert! integral_sin_pow_even_mul_cos_pow_even 1 1 using 1
  have h1 : forall c : Real, (↑1 - c) / ↑2 * ((↑1 + c) / ↑2) = (↑1 - c ^ 2) / 4 := fun c => by ring
  have h2 : Continuous fun x => cos (2 * x) ^ 2 := by fun_prop
  have h3 : forall x, cos x * sin x = sin (2 * x) / 2 := by intro; rw [sin_two_mul]; ring
  have h4 : forall d : Real, 2 * (2 * d) = 4 * d := fun d => by ring
  simp [h1, h2.intervalIntegrable, integral_comp_mul_left fun x => cos x ^ 2, h3, h4]
  ring


/--
theorem `integral_sqrt_one_sub_sq` / 定理 `integral_sqrt_one_sub_sq`

English:
theorem integral_sqrt_one_sub_sq
  statement: ∫ x in (-1 : Real)..1, √(1 - x ^ 2 : Real) = π / 2
  proof: calc
    _ = ∫ x in sin (-(π / 2))..sin (π / 2), √(1 - x ^ 2 : Real) := by rw [sin_neg, sin_pi_div_two]
    _ = ∫ x in (-(π / 2))..(π / 2), √(1 - sin x ^ 2 : Real) * cos x :=
          (integral_comp_mul_deriv (fun x _ => hasDerivAt_sin x) continuousOn_cos
            (by fun_prop)).symm
    _ = ∫ x

中文:
定理 integral_sqrt_one_sub_sq
  结论: ∫ x in (-1 : 实数)..1, √(1 - x ^ 2 : 实数) = π / 2
  证明: calc
    _ = ∫ x in sin (-(π / 2))..sin (π / 2), √(1 - x ^ 2 : Real) := by rw [sin_neg, sin_pi_div_two]
    _ = ∫ x in (-(π / 2))..(π / 2), √(1 - sin x ^ 2 : Real) * cos x :=
          (integral_comp_mul_deriv (fun x _ => hasDerivAt_sin x) continuousOn_cos
            (by fun_prop)).symm
    _ = ∫ x

Depends on / 依赖: MeasureTheory, MeasureTheory.ae_of_all, Real.cos_eq_sqrt_one_sub_sin_sq, Real.pi_pos, Set.mem_Ioc, ae_of_all, continuousOn_cos, cos_eq_sqrt_one_sub_sin_sq, fun_prop, half_pos, hasDerivAt_sin, integral_comp_mul_deriv, integral_congr_ae, le_of_lt, mem_Ioc, neg_le_self, pi_pos, sin_neg, sin_pi_div_two, uIoc_of_le
-/
theorem integral_sqrt_one_sub_sq : ∫ x in (-1 : Real)..1, √(1 - x ^ 2 : Real) = π / 2 :=
  calc
    _ = ∫ x in sin (-(π / 2))..sin (π / 2), √(1 - x ^ 2 : Real) := by rw [sin_neg, sin_pi_div_two]
    _ = ∫ x in (-(π / 2))..(π / 2), √(1 - sin x ^ 2 : Real) * cos x :=
          (integral_comp_mul_deriv (fun x _ => hasDerivAt_sin x) continuousOn_cos
            (by fun_prop)).symm
    _ = ∫ x in (-(π / 2))..(π / 2), cos x ^ 2 := by
          refine integral_congr_ae (MeasureTheory.ae_of_all _ fun _ h => ?_)
          rw [uIoc_of_le (neg_le_self (le_of_lt (half_pos Real.pi_pos)))]; rw [Set.mem_Ioc] at h
          rw [← Real.cos_eq_sqrt_one_sub_sin_sq (le_of_lt h.1) h.2]; rw [pow_two]
    _ = π / 2 := by simp
