/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.DSlope

/-!
# Sinc function

This file contains the definition of the sinc function and some of its properties.

## Main definitions

* `Real.sinc`: the (unnormalized) sinc function, defined as `sinc x = sin x / x` for `x ≠ 0`
  and `1` for `x = 0`.

## Main statements

* `continuous_sinc`: the sinc function is continuous.

-/

@[expose] public section

open Filter
open scoped Topology

namespace Real

variable {x : Real}

/-- The function `sin x / x` modified to take the value 1 at 0, which makes it continuous. -/
@[pp_nodot]
/--
Definition of `sinc` / `sinc` 的定义

English:
definition sinc
  signature: (x : Real)
  body: if x = 0 then 1 else sin x / x

中文:
定义 sinc
  签名: (x : 实数)
  定义体: if x = 0 then 1 else sin x / x
-/
noncomputable def sinc (x : Real) : Real := if x = 0 then 1 else sin x / x

/--
lemma `sinc_apply` / 引理 `sinc_apply`

English:
lemma sinc_apply
  statement: sinc x = if x = 0 then 1 else sin x / x
  proof: rfl

@[simp]

中文:
引理 sinc_apply
  结论: sinc x = if x = 0 then 1 else sin x / x
  证明: rfl

@[simp]
-/
lemma sinc_apply : sinc x = if x = 0 then 1 else sin x / x := rfl

@[simp]
/--
lemma `sinc_zero` / 引理 `sinc_zero`

English:
lemma sinc_zero
  statement: sinc 0 = 1
  proof: by simp [sinc]

中文:
引理 sinc_zero
  结论: sinc 0 = 1
  证明: by simp [sinc]
-/
lemma sinc_zero : sinc 0 = 1 := by simp [sinc]

/--
lemma `sinc_of_ne_zero` / 引理 `sinc_of_ne_zero`

English:
lemma sinc_of_ne_zero
  given: (hx : x != 0)
  statement: sinc x = sin x / x
  proof: by simp [sinc, hx]

中文:
引理 sinc_of_ne_zero
  条件: (hx : x != 0)
  结论: sinc x = sin x / x
  证明: by simp [sinc, hx]
-/
lemma sinc_of_ne_zero (hx : x != 0) : sinc x = sin x / x := by simp [sinc, hx]

/--
lemma `sinc_eq_dslope` / 引理 `sinc_eq_dslope`

English:
lemma sinc_eq_dslope
  statement: sinc = dslope sin 0
  proof: by
  ext
  simp [dslope, Function.update_apply, sinc, slope, div_eq_inv_mul]

@[simp]

中文:
引理 sinc_eq_dslope
  结论: sinc = dslope sin 0
  证明: by
  ext
  simp [dslope, Function.update_apply, sinc, slope, div_eq_inv_mul]

@[simp]

Depends on / 依赖: Function, Function.update_apply, div_eq_inv_mul, dslope, update_apply
-/
lemma sinc_eq_dslope : sinc = dslope sin 0 := by
  ext
  simp [dslope, Function.update_apply, sinc, slope, div_eq_inv_mul]

@[simp]
/--
lemma `sinc_neg` / 引理 `sinc_neg`

English:
lemma sinc_neg
  given: (x : Real)
  statement: sinc (-x) = sinc x
  proof: by
  by_cases hx : x = 0
  · simp [hx]
  · simp [sinc_of_ne_zero hx, sinc_of_ne_zero (neg_ne_zero.mpr hx)]

中文:
引理 sinc_neg
  条件: (x : 实数)
  结论: sinc (-x) = sinc x
  证明: by
  by_cases hx : x = 0
  · simp [hx]
  · simp [sinc_of_ne_zero hx, sinc_of_ne_zero (neg_ne_zero.mpr hx)]

Depends on / 依赖: X.obj, Y.obj, neg_ne_zero, neg_ne_zero.mpr, sinc_of_ne_zero
-/
lemma sinc_neg (x : Real) : sinc (-x) = sinc x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [sinc_of_ne_zero hx, sinc_of_ne_zero (neg_ne_zero.mpr hx)]

/--
lemma `abs_sinc_le_one` / 引理 `abs_sinc_le_one`

English:
lemma abs_sinc_le_one
  given: (x : Real)
  statement: |sinc x| <= 1
  proof: by
  by_cases hx : x = 0
  · simp [hx]
  rw [sinc_of_ne_zero hx]; rw [abs_div]
  refine div_le_of_le_mul₀ (abs_nonneg _) zero_le_one ?_
  rw [one_mul]
  exact abs_sin_le_abs

中文:
引理 abs_sinc_le_one
  条件: (x : 实数)
  结论: |sinc x| <= 1
  证明: by
  by_cases hx : x = 0
  · simp [hx]
  rw [sinc_of_ne_zero hx]; rw [abs_div]
  refine div_le_of_le_mul₀ (abs_nonneg _) zero_le_one ?_
  rw [one_mul]
  exact abs_sin_le_abs

Depends on / 依赖: abs_div, abs_nonneg, abs_sin_le_abs, one_mul, sinc_of_ne_zero, zero_le_one
-/
lemma abs_sinc_le_one (x : Real) : |sinc x| <= 1 := by
  by_cases hx : x = 0
  · simp [hx]
  rw [sinc_of_ne_zero hx]; rw [abs_div]
  refine div_le_of_le_mul₀ (abs_nonneg _) zero_le_one ?_
  rw [one_mul]
  exact abs_sin_le_abs

/--
lemma `sinc_le_one` / 引理 `sinc_le_one`

English:
lemma sinc_le_one
  given: (x : Real)
  statement: sinc x <= 1
  proof: (abs_le.mp (abs_sinc_le_one x)).2

中文:
引理 sinc_le_one
  条件: (x : 实数)
  结论: sinc x <= 1
  证明: (abs_le.mp (abs_sinc_le_one x)).2

Depends on / 依赖: abs_le, abs_le.mp, abs_sinc_le_one
-/
lemma sinc_le_one (x : Real) : sinc x <= 1 := (abs_le.mp (abs_sinc_le_one x)).2

/--
lemma `neg_one_le_sinc` / 引理 `neg_one_le_sinc`

English:
lemma neg_one_le_sinc
  given: (x : Real)
  statement: -1 <= sinc x
  proof: (abs_le.mp (abs_sinc_le_one x)).1

中文:
引理 neg_one_le_sinc
  条件: (x : 实数)
  结论: -1 <= sinc x
  证明: (abs_le.mp (abs_sinc_le_one x)).1

Depends on / 依赖: abs_le, abs_le.mp, abs_sinc_le_one
-/
lemma neg_one_le_sinc (x : Real) : -1 <= sinc x := (abs_le.mp (abs_sinc_le_one x)).1

/--
lemma `sin_div_le_inv_abs` / 引理 `sin_div_le_inv_abs`

English:
lemma sin_div_le_inv_abs
  given: (x : Real)
  statement: sin x / x <= |x|⁻¹
  proof: by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [abs_of_nonpos hx.le, ← one_div, le_div_iff₀, div_eq_mul_inv]
    · ring_nf
      rw [mul_assoc]; rw [mul_inv_cancel₀ hx.ne]; rw [mul_one]; rw [neg_le]
      exact neg_one_le_sin x
    · simpa using hx
  · simp
  · rw [abs_of_nonneg hx.le, div_

中文:
引理 sin_div_le_inv_abs
  条件: (x : 实数)
  结论: sin x / x <= |x|⁻¹
  证明: by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [abs_of_nonpos hx.le, ← one_div, le_div_iff₀, div_eq_mul_inv]
    · ring_nf
      rw [mul_assoc]; rw [mul_inv_cancel₀ hx.ne]; rw [mul_one]; rw [neg_le]
      exact neg_one_le_sin x
    · simpa using hx
  · simp
  · rw [abs_of_nonneg hx.le, div_

Depends on / 依赖: abs_of_nonneg, abs_of_nonpos, div_eq_mul_inv, hx.le, hx.ne, lt_trichotomy, mul_assoc, mul_one, neg_le, neg_one_le_sin, one_div, ring_nf, sin_le_one
-/
lemma sin_div_le_inv_abs (x : Real) : sin x / x <= |x|⁻¹ := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [abs_of_nonpos hx.le, ← one_div, le_div_iff₀, div_eq_mul_inv]
    · ring_nf
      rw [mul_assoc]; rw [mul_inv_cancel₀ hx.ne]; rw [mul_one]; rw [neg_le]
      exact neg_one_le_sin x
    · simpa using hx
  · simp
  · rw [abs_of_nonneg hx.le, div_eq_mul_inv, mul_inv_le_iff₀ hx, inv_mul_cancel₀ hx.ne']
    exact sin_le_one x

/--
lemma `sinc_le_inv_abs` / 引理 `sinc_le_inv_abs`

English:
lemma sinc_le_inv_abs
  given: (hx : x != 0)
  statement: sinc x <= |x|⁻¹
  proof: by
  rw [sinc_of_ne_zero hx]
  exact sin_div_le_inv_abs x

中文:
引理 sinc_le_inv_abs
  条件: (hx : x != 0)
  结论: sinc x <= |x|⁻¹
  证明: by
  rw [sinc_of_ne_zero hx]
  exact sin_div_le_inv_abs x

Depends on / 依赖: sin_div_le_inv_abs, sinc_of_ne_zero
-/
lemma sinc_le_inv_abs (hx : x != 0) : sinc x <= |x|⁻¹ := by
  rw [sinc_of_ne_zero hx]
  exact sin_div_le_inv_abs x

/-- The function `sinc` is continuous. -/
@[fun_prop]
/--
lemma `continuous_sinc` / 引理 `continuous_sinc`

English:
lemma continuous_sinc
  statement: Continuous sinc
  proof: by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  rw [sinc_eq_dslope]
  by_cases hx : x = 0
  · simp [hx]
  · rw [continuousAt_dslope_of_ne hx]
    fun_prop

中文:
引理 continuous_sinc
  结论: Continuous sinc
  证明: by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  rw [sinc_eq_dslope]
  by_cases hx : x = 0
  · simp [hx]
  · rw [continuousAt_dslope_of_ne hx]
    fun_prop

Depends on / 依赖: continuousAt_dslope_of_ne, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr, fun_prop, sinc_eq_dslope
-/
lemma continuous_sinc : Continuous sinc := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  rw [sinc_eq_dslope]
  by_cases hx : x = 0
  · simp [hx]
  · rw [continuousAt_dslope_of_ne hx]
    fun_prop

end Real
