/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Slope
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Some properties of the interval integral of `fun x ↦ slope f x (x + c)`, given a constant `c : ℝ`

This file proves that:
* `IntervalIntegrable.intervalIntegrable_slope`: If `f` is interval integrable on `a..(b + c)`
  where `a ≤ b` and `0 ≤ c`, then `fun x ↦ slope f x (x + c)` is interval integrable on `a..b`.
* `MonotoneOn.intervalIntegrable_slope`: If `f` is monotone on `a..(b + c)`
  where `a ≤ b` and `0 ≤ c`, then `fun x ↦ slope f x (x + c)` is interval integrable on `a..b`.
* `MonotoneOn.intervalIntegral_slope_le`: If `f` is monotone on `a..(b + c)`
  where `a ≤ b` and `0 ≤ c`, then the interval integral of `fun x ↦ slope f x (x + c)` on `a..b` is
  at most `f (b + c) - f a`.

## Tags
interval integrable, interval integral, monotone, slope
-/

public section

open MeasureTheory Set

/--
theorem `IntervalIntegrable.intervalIntegrable_slope` / 定理 `IntervalIntegrable.intervalIntegrable_slope`

English:
theorem IntervalIntegrable.intervalIntegrable_slope
  statement: {f : Real -> Real} {a b c : Real}
  proof: by
  simp only [slope, add_sub_cancel_left, vsub_eq_sub, smul_eq_mul]
.sub (hf.mono_set (by grind [uIcc])) .mono_set (by grind [uIcc]) exact hf.comp_add_right c
.const_mul (c := c⁻¹)

中文:
定理 整数erval整数egrable.interval整数egrable_slope
  结论: {f : 实数 -> 实数} {a b c : 实数}
  证明: by
  simp only [slope, add_sub_cancel_left, vsub_eq_sub, smul_eq_mul]
.sub (hf.mono_set (by grind [uIcc])) .mono_set (by grind [uIcc]) exact hf.comp_add_right c
.const_mul (c := c⁻¹)

Depends on / 依赖: add_sub_cancel_left, comp_add_right, const_mul, hf.comp_add_right, hf.mono_set, mono_set, smul_eq_mul, vsub_eq_sub
-/
theorem IntervalIntegrable.intervalIntegrable_slope {f : Real -> Real} {a b c : Real}
    (hf : IntervalIntegrable f volume a (b + c)) (hab : a <= b) (hc : 0 <= c) :
    IntervalIntegrable (fun x => slope f x (x + c)) volume a b := by
  simp only [slope, add_sub_cancel_left, vsub_eq_sub, smul_eq_mul]
.sub (hf.mono_set (by grind [uIcc])) .mono_set (by grind [uIcc]) exact hf.comp_add_right c
.const_mul (c := c⁻¹)

/--
theorem `MonotoneOn.intervalIntegrable_slope` / 定理 `MonotoneOn.intervalIntegrable_slope`

English:
theorem MonotoneOn.intervalIntegrable_slope
  statement: {f : Real -> Real} {a b c : Real}
  proof: .intervalIntegrable.intervalIntegrable_slope hab hc uIcc_of_le (show a <= b + c by linarith) ▸ hf

中文:
定理 MonotoneOn.interval整数egrable_slope
  结论: {f : 实数 -> 实数} {a b c : 实数}
  证明: .intervalIntegrable.intervalIntegrable_slope hab hc uIcc_of_le (show a <= b + c by linarith) ▸ hf

Depends on / 依赖: intervalIntegrable, intervalIntegrable.intervalIntegrable_slope, intervalIntegrable_slope, uIcc_of_le
-/
theorem MonotoneOn.intervalIntegrable_slope {f : Real -> Real} {a b c : Real}
    (hf : MonotoneOn f (Icc a (b + c))) (hab : a <= b) (hc : 0 <= c) :
    IntervalIntegrable (fun x => slope f x (x + c)) volume a b :=
.intervalIntegrable.intervalIntegrable_slope hab hc uIcc_of_le (show a <= b + c by linarith) ▸ hf

/--
theorem `MonotoneOn.intervalIntegral_slope_le` / 定理 `MonotoneOn.intervalIntegral_slope_le`

English:
theorem MonotoneOn.intervalIntegral_slope_le
  statement: {f : Real -> Real} {a b c : Real}
  proof: by
  rcases eq_or_lt_of_le hc with hc | hc
  · simp only [← hc, add_zero, slope_same, intervalIntegral.integral_zero, sub_nonneg]
    apply hf <;> grind
  rw [← uIcc_of_le (by linarith)] at hf
  have hf' := hf.intervalIntegrable (μ := volume)
  simp only [slope, add_sub_cancel_left, vsub_eq_sub, smu

中文:
定理 MonotoneOn.interval整数egral_slope_le
  结论: {f : 实数 -> 实数} {a b c : 实数}
  证明: by
  rcases eq_or_lt_of_le hc with hc | hc
  · simp only [← hc, add_zero, slope_same, intervalIntegral.integral_zero, sub_nonneg]
    apply hf <;> grind
  rw [← uIcc_of_le (by linarith)] at hf
  have hf' := hf.intervalIntegrable (μ := volume)
  simp only [slope, add_sub_cancel_left, vsub_eq_sub, smu

Depends on / 依赖: add_sub_cancel_left, add_zero, comp_add_right, eq_or_lt_of_le, hf.intervalIntegrable, integral_comp_add_right, integral_const_mul, integral_sub, integral_zero, intervalIntegrable, intervalIntegral, intervalIntegral.integral_comp_add_right, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub, intervalIntegral.integral_zero, mono_set, slope_same, smul_eq_mul, sub_nonneg, uIcc_of_le
-/
theorem MonotoneOn.intervalIntegral_slope_le {f : Real -> Real} {a b c : Real}
    (hf : MonotoneOn f (Icc a (b + c))) (hab : a <= b) (hc : 0 <= c) :
    ∫ x in a..b, slope f x (x + c) <= f (b + c) - f a := by
  rcases eq_or_lt_of_le hc with hc | hc
  · simp only [← hc, add_zero, slope_same, intervalIntegral.integral_zero, sub_nonneg]
    apply hf <;> grind
  rw [← uIcc_of_le (by linarith)] at hf
  have hf' := hf.intervalIntegrable (μ := volume)
  simp only [slope, add_sub_cancel_left, vsub_eq_sub, smul_eq_mul,
    intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub
        (hf'.comp_add_right c |>.mono_set (by grind [uIcc]))
        (hf'.mono_set (by grind [uIcc])),
      intervalIntegral.integral_comp_add_right,
      intervalIntegral.integral_interval_sub_interval_comm'
        (hf'.mono_set (by grind [uIcc]))
        (hf'.mono_set (by grind [uIcc]))
        (hf'.mono_set (by grind [uIcc]))]
  have fU : ∫ (x : Real) in b..b + c, f x <= c * f (b + c) := by
    grw [intervalIntegral.integral_mono_on (g := fun _ => f (b + c))
          (by linarith)
          (hf'.mono_set (by grind [uIcc]))
          (by simp)
          (by intros; apply hf <;> grind [uIcc])]
    simp
  have fL : c * f a <= ∫ (x : Real) in a..a + c, f x := by
    grw [← intervalIntegral.integral_mono_on (f := fun _ => f a)
            (by linarith)
            (by simp)
            (hf'.mono_set (by grind [uIcc]))
            (by intros; apply hf <;> grind [uIcc])]
    simp
  grw [fU, ← fL]
  field_simp; rfl
