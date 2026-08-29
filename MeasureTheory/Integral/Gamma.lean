/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Integrals involving the Gamma function

In this file, we collect several integrals over `ℝ` or `ℂ` that evaluate in terms of the
`Real.Gamma` function.

-/

public section

open Real Set MeasureTheory MeasureTheory.Measure

section real

/--
theorem `integral_rpow_mul_exp_neg_rpow` / 定理 `integral_rpow_mul_exp_neg_rpow`

English:
theorem integral_rpow_mul_exp_neg_rpow
  given: {p q : Real} (hp : 0 < p) (hq : -1 < q)
  proof: by
  calc
    _ = ∫ (x : Real) in Ioi 0, (1 / p * x ^ (1 / p - 1)) • ((x ^ (1 / p)) ^ q * exp (-x)) := by
      rw [← integral_comp_rpow_Ioi _ (one_div_ne_zero (ne_of_gt hp))]; rw [abs_eq_self.mpr (le_of_lt (one_div_pos.mpr hp))]
      refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
      rw [← rpow_mul (le_of_lt hx) _ p]; rw [one_div_mul_cancel (ne_of_gt hp)]; rw [rpow_one]
    _ = ∫ (x : Real) in Ioi 0, 1 / p * exp (-x) * x ^ (1 / p - 1 + q / p) := by
      simp_rw [smul_eq_mul, mul_assoc]
      refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
      rw [← rpow_mul (le_of_lt hx)]; rw [div_mul_eq_mul_div]; rw [one_mul]; rw [rpow_add hx]
      ring_nf
    _ = (1 / p) * Gamma ((q + 1) / p) := by
      rw [Gamma_eq_integral (div_pos (neg_lt_iff_pos_add.mp hq) hp)]
      simp_rw [show 1 / p - 1 + q / p = (q + 1) / p - 1 by ring, ← integral_const_mul,
        ← mul_assoc]

中文:
定理 integral_rpow_mul_exp_neg_rpow
  条件: {p q : 实数} (hp : 0 < p) (hq : -1 < q)
  证明: by
  calc
    _ = ∫ (x : Real) in Ioi 0, (1 / p * x ^ (1 / p - 1)) • ((x ^ (1 / p)) ^ q * exp (-x)) := by
      rw [← integral_comp_rpow_Ioi _ (one_div_ne_zero (ne_of_gt hp))]; rw [abs_eq_self.mpr (le_of_lt (one_div_pos.mpr hp))]
      refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
      rw [← rpow_mul (le_of_lt hx) _ p]; rw [one_div_mul_cancel (ne_of_gt hp)]; rw [rpow_one]
    _ = ∫ (x : Real) in Ioi 0, 1 / p * exp (-x) * x ^ (1 / p - 1 + q / p) := by
      simp_rw [smul_eq_mul, mul_assoc]
      refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
      rw [← rpow_mul (le_of_lt hx)]; rw [div_mul_eq_mul_div]; rw [one_mul]; rw [rpow_add hx]
      ring_nf
    _ = (1 / p) * Gamma ((q + 1) / p) := by
      rw [Gamma_eq_integral (div_pos (neg_lt_iff_pos_add.mp hq) hp)]
      simp_rw [show 1 / p - 1 + q / p = (q + 1) / p - 1 by ring, ← integral_const_mul,
        ← mul_assoc]

Depends on / 依赖: abs_eq_self, abs_eq_self.mpr, integral_comp_rpow_Ioi, le_of_lt, measurableSet_Ioi, mul_assoc, ne_of_gt, one_div_mul_cancel, one_div_ne_zero, one_div_pos, one_div_pos.mpr, rpow_mul, rpow_one, setIntegral_co, setIntegral_congr_fun, simp_rw, smul_eq_mul
-/
theorem integral_rpow_mul_exp_neg_rpow {p q : Real} (hp : 0 < p) (hq : -1 < q) :
    ∫ x in Ioi (0 : Real), x ^ q * exp (-x ^ p) = (1 / p) * Gamma ((q + 1) / p) := by
  calc
    _ = ∫ (x : Real) in Ioi 0, (1 / p * x ^ (1 / p - 1)) • ((x ^ (1 / p)) ^ q * exp (-x)) := by
      rw [← integral_comp_rpow_Ioi _ (one_div_ne_zero (ne_of_gt hp))]; rw [abs_eq_self.mpr (le_of_lt (one_div_pos.mpr hp))]
      refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
      rw [← rpow_mul (le_of_lt hx) _ p]; rw [one_div_mul_cancel (ne_of_gt hp)]; rw [rpow_one]
    _ = ∫ (x : Real) in Ioi 0, 1 / p * exp (-x) * x ^ (1 / p - 1 + q / p) := by
      simp_rw [smul_eq_mul, mul_assoc]
      refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
      rw [← rpow_mul (le_of_lt hx)]; rw [div_mul_eq_mul_div]; rw [one_mul]; rw [rpow_add hx]
      ring_nf
    _ = (1 / p) * Gamma ((q + 1) / p) := by
      rw [Gamma_eq_integral (div_pos (neg_lt_iff_pos_add.mp hq) hp)]
      simp_rw [show 1 / p - 1 + q / p = (q + 1) / p - 1 by ring, ← integral_const_mul,
        ← mul_assoc]

/--
theorem `integral_rpow_mul_exp_neg_mul_rpow` / 定理 `integral_rpow_mul_exp_neg_mul_rpow`

English:
theorem integral_rpow_mul_exp_neg_mul_rpow
  given: {p q b : Real} (hp : 0 < p) (hq : -1 < q) (hb : 0 < b)
  proof: by
  calc
    _ = ∫ x in Ioi (0 : Real), b ^ (-p⁻¹ * q) * ((b ^ p⁻¹ * x) ^ q * rexp (-(b ^ p⁻¹ * x) ^ p)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
      rw [mul_rpow _ (le_of_lt hx)]; rw [mul_rpow _ (le_of_lt hx)]; rw [← rpow_mul]; rw [← rpow_mul]; rw [inv_mul_cancel₀]; rw [rpow_one]; rw [mul_assoc]; rw [← mul_assoc]; rw [← rpow_add]; rw [neg_mul p⁻¹]; rw [neg_add_cancel]; rw [rpow_zero]; rw [one_mul]; rw [neg_mul]
      all_goals positivity
    _ = (b ^ p⁻¹)⁻¹ * ∫ x in Ioi (0 : Real), b ^ (-p⁻¹ * q) * (x ^ q * rexp (-x ^ p)) := by
      rw [integral_comp_mul_left_Ioi (fun x => b ^ (-p⁻¹ * q) * (x ^ q * exp (-x ^ p))) 0]; rw [mul_zero]; rw [smul_eq_mul]
      all_goals positivity
    _ = b ^ (-(q + 1) / p) * (1 / p) * Gamma ((q + 1) / p) := by
      rw [integral_const_mul]; rw [integral_rpow_mul_exp_neg_rpow _ hq]; rw [mul_assoc]; rw [← mul_assoc]; rw [← rpow_neg_one]; rw [← rpow_mul]; rw [← rpow_add]
      · congr; ring
      all_goals positivity

中文:
定理 integral_rpow_mul_exp_neg_mul_rpow
  条件: {p q b : 实数} (hp : 0 < p) (hq : -1 < q) (hb : 0 < b)
  证明: by
  calc
    _ = ∫ x in Ioi (0 : Real), b ^ (-p⁻¹ * q) * ((b ^ p⁻¹ * x) ^ q * rexp (-(b ^ p⁻¹ * x) ^ p)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
      rw [mul_rpow _ (le_of_lt hx)]; rw [mul_rpow _ (le_of_lt hx)]; rw [← rpow_mul]; rw [← rpow_mul]; rw [inv_mul_cancel₀]; rw [rpow_one]; rw [mul_assoc]; rw [← mul_assoc]; rw [← rpow_add]; rw [neg_mul p⁻¹]; rw [neg_add_cancel]; rw [rpow_zero]; rw [one_mul]; rw [neg_mul]
      all_goals positivity
    _ = (b ^ p⁻¹)⁻¹ * ∫ x in Ioi (0 : Real), b ^ (-p⁻¹ * q) * (x ^ q * rexp (-x ^ p)) := by
      rw [integral_comp_mul_left_Ioi (fun x => b ^ (-p⁻¹ * q) * (x ^ q * exp (-x ^ p))) 0]; rw [mul_zero]; rw [smul_eq_mul]
      all_goals positivity
    _ = b ^ (-(q + 1) / p) * (1 / p) * Gamma ((q + 1) / p) := by
      rw [integral_const_mul]; rw [integral_rpow_mul_exp_neg_rpow _ hq]; rw [mul_assoc]; rw [← mul_assoc]; rw [← rpow_neg_one]; rw [← rpow_mul]; rw [← rpow_add]
      · congr; ring
      all_goals positivity

Depends on / 依赖: all_goals, le_of_lt, measurableSet_Ioi, mul_assoc, mul_rpow, neg_add_cancel, neg_mul, one_mul, rpow_add, rpow_mul, rpow_one, rpow_zero, setIntegral_congr_fun
-/
theorem integral_rpow_mul_exp_neg_mul_rpow {p q b : Real} (hp : 0 < p) (hq : -1 < q) (hb : 0 < b) :
    ∫ x in Ioi (0 : Real), x ^ q * exp (-b * x ^ p) =
      b ^ (-(q + 1) / p) * (1 / p) * Gamma ((q + 1) / p) := by
  calc
    _ = ∫ x in Ioi (0 : Real), b ^ (-p⁻¹ * q) * ((b ^ p⁻¹ * x) ^ q * rexp (-(b ^ p⁻¹ * x) ^ p)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
      rw [mul_rpow _ (le_of_lt hx)]; rw [mul_rpow _ (le_of_lt hx)]; rw [← rpow_mul]; rw [← rpow_mul]; rw [inv_mul_cancel₀]; rw [rpow_one]; rw [mul_assoc]; rw [← mul_assoc]; rw [← rpow_add]; rw [neg_mul p⁻¹]; rw [neg_add_cancel]; rw [rpow_zero]; rw [one_mul]; rw [neg_mul]
      all_goals positivity
    _ = (b ^ p⁻¹)⁻¹ * ∫ x in Ioi (0 : Real), b ^ (-p⁻¹ * q) * (x ^ q * rexp (-x ^ p)) := by
      rw [integral_comp_mul_left_Ioi (fun x => b ^ (-p⁻¹ * q) * (x ^ q * exp (-x ^ p))) 0]; rw [mul_zero]; rw [smul_eq_mul]
      all_goals positivity
    _ = b ^ (-(q + 1) / p) * (1 / p) * Gamma ((q + 1) / p) := by
      rw [integral_const_mul]; rw [integral_rpow_mul_exp_neg_rpow _ hq]; rw [mul_assoc]; rw [← mul_assoc]; rw [← rpow_neg_one]; rw [← rpow_mul]; rw [← rpow_add]
      · congr; ring
      all_goals positivity

/--
theorem `integral_exp_neg_rpow` / 定理 `integral_exp_neg_rpow`

English:
theorem integral_exp_neg_rpow
  given: {p : Real} (hp : 0 < p)
  proof: by
  convert! (integral_rpow_mul_exp_neg_rpow hp neg_one_lt_zero) using 1
  · simp_rw [rpow_zero, one_mul]
  · rw [zero_add, Gamma_add_one (one_div_ne_zero (ne_of_gt hp))]

中文:
定理 integral_exp_neg_rpow
  条件: {p : 实数} (hp : 0 < p)
  证明: by
  convert! (integral_rpow_mul_exp_neg_rpow hp neg_one_lt_zero) using 1
  · simp_rw [rpow_zero, one_mul]
  · rw [zero_add, Gamma_add_one (one_div_ne_zero (ne_of_gt hp))]

Depends on / 依赖: Gamma_add_one, convert, integral_rpow_mul_exp_neg_rpow, ne_of_gt, neg_one_lt_zero, one_div_ne_zero, one_mul, rpow_zero, simp_rw, zero_add
-/
theorem integral_exp_neg_rpow {p : Real} (hp : 0 < p) :
    ∫ x in Ioi (0 : Real), exp (-x ^ p) = Gamma (1 / p + 1) := by
  convert! (integral_rpow_mul_exp_neg_rpow hp neg_one_lt_zero) using 1
  · simp_rw [rpow_zero, one_mul]
  · rw [zero_add, Gamma_add_one (one_div_ne_zero (ne_of_gt hp))]

/--
theorem `integral_exp_neg_mul_rpow` / 定理 `integral_exp_neg_mul_rpow`

English:
theorem integral_exp_neg_mul_rpow
  given: {p b : Real} (hp : 0 < p) (hb : 0 < b)
  proof: by
  convert! (integral_rpow_mul_exp_neg_mul_rpow hp neg_one_lt_zero hb) using 1
  · simp_rw [rpow_zero, one_mul]
  · rw [zero_add, Gamma_add_one (one_div_ne_zero (ne_of_gt hp)), mul_assoc]

中文:
定理 integral_exp_neg_mul_rpow
  条件: {p b : 实数} (hp : 0 < p) (hb : 0 < b)
  证明: by
  convert! (integral_rpow_mul_exp_neg_mul_rpow hp neg_one_lt_zero hb) using 1
  · simp_rw [rpow_zero, one_mul]
  · rw [zero_add, Gamma_add_one (one_div_ne_zero (ne_of_gt hp)), mul_assoc]

Depends on / 依赖: Gamma_add_one, convert, integral_rpow_mul_exp_neg_mul_rpow, mul_assoc, ne_of_gt, neg_one_lt_zero, one_div_ne_zero, one_mul, rpow_zero, simp_rw, zero_add
-/
theorem integral_exp_neg_mul_rpow {p b : Real} (hp : 0 < p) (hb : 0 < b) :
    ∫ x in Ioi (0 : Real), exp (-b * x ^ p) = b ^ (-1 / p) * Gamma (1 / p + 1) := by
  convert! (integral_rpow_mul_exp_neg_mul_rpow hp neg_one_lt_zero hb) using 1
  · simp_rw [rpow_zero, one_mul]
  · rw [zero_add, Gamma_add_one (one_div_ne_zero (ne_of_gt hp)), mul_assoc]

end real

section complex

/--
theorem `Complex.integral_rpow_mul_exp_neg_rpow` / 定理 `Complex.integral_rpow_mul_exp_neg_rpow`

English:
theorem Complex.integral_rpow_mul_exp_neg_rpow
  given: {p q : Real} (hp : 1 <= p) (hq : -2 < q)
  proof: by
  calc
    _ = ∫ x in Ioi (0 : Real) ×ˢ Ioo (-π) π, x.1 * (|x.1| ^ q * rexp (-|x.1| ^ p)) := by
      rw [← Complex.integral_comp_polarCoord_symm]; rw [polarCoord_target]
      simp_rw [Complex.norm_polarCoord_symm, smul_eq_mul]
    _ = (∫ x in Ioi (0 : Real), x * |x| ^ q * rexp (-|x| ^ p)) * ∫ _ in Ioo (-π) π, 1 := by
      rw [← setIntegral_prod_mul]; rw [volume_eq_prod]
      simp_rw [mul_one]
      congr! 2; ring
    _ = 2 * π * ∫ x in Ioi (0 : Real), x * |x| ^ q * rexp (-|x| ^ p) := by
      simp_rw [integral_const, measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter,
        volume_real_Ioo_of_le (a := -π) (b := π) (by linarith [pi_nonneg]),
        sub_neg_eq_add, ← two_mul, smul_eq_mul, mul_one, mul_comm]
    _ = 2 * π * ∫ x in Ioi (0 : Real), x ^ (q + 1) * rexp (-x ^ p) := by
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [mem_Ioi] at hx
      rw [abs_eq_self.mpr hx.le]; rw [rpow_add hx]; rw [rpow_one]
      ring
    _ = (2 * Real.pi / p) * Real.Gamma ((q + 2) / p) := by
      rw [_root_.integral_rpow_mul_exp_neg_rpow (by linarith) (by linarith)]; rw [add_assoc]; rw [one_add_one_eq_two]
      ring

中文:
定理 复形.integral_rpow_mul_exp_neg_rpow
  条件: {p q : 实数} (hp : 1 <= p) (hq : -2 < q)
  证明: by
  calc
    _ = ∫ x in Ioi (0 : Real) ×ˢ Ioo (-π) π, x.1 * (|x.1| ^ q * rexp (-|x.1| ^ p)) := by
      rw [← Complex.integral_comp_polarCoord_symm]; rw [polarCoord_target]
      simp_rw [Complex.norm_polarCoord_symm, smul_eq_mul]
    _ = (∫ x in Ioi (0 : Real), x * |x| ^ q * rexp (-|x| ^ p)) * ∫ _ in Ioo (-π) π, 1 := by
      rw [← setIntegral_prod_mul]; rw [volume_eq_prod]
      simp_rw [mul_one]
      congr! 2; ring
    _ = 2 * π * ∫ x in Ioi (0 : Real), x * |x| ^ q * rexp (-|x| ^ p) := by
      simp_rw [integral_const, measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter,
        volume_real_Ioo_of_le (a := -π) (b := π) (by linarith [pi_nonneg]),
        sub_neg_eq_add, ← two_mul, smul_eq_mul, mul_one, mul_comm]
    _ = 2 * π * ∫ x in Ioi (0 : Real), x ^ (q + 1) * rexp (-x ^ p) := by
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [mem_Ioi] at hx
      rw [abs_eq_self.mpr hx.le]; rw [rpow_add hx]; rw [rpow_one]
      ring
    _ = (2 * Real.pi / p) * Real.Gamma ((q + 2) / p) := by
      rw [_root_.integral_rpow_mul_exp_neg_rpow (by linarith) (by linarith)]; rw [add_assoc]; rw [one_add_one_eq_two]
      ring

Depends on / 依赖: Complex.integral_comp_polarCoord_symm, Complex.norm_polarCoord_symm, integral_comp_polarCoord_symm, integral_const, measureReal_restrict, mul_one, norm_polarCoord_symm, polarCoord_target, setIntegral_prod_mul, simp_rw, smul_eq_mul, volume_eq_prod
-/
theorem Complex.integral_rpow_mul_exp_neg_rpow {p q : Real} (hp : 1 <= p) (hq : -2 < q) :
    ∫ x : Complex, ‖x‖ ^ q * rexp (-‖x‖ ^ p) = (2 * π / p) * Real.Gamma ((q + 2) / p) := by
  calc
    _ = ∫ x in Ioi (0 : Real) ×ˢ Ioo (-π) π, x.1 * (|x.1| ^ q * rexp (-|x.1| ^ p)) := by
      rw [← Complex.integral_comp_polarCoord_symm]; rw [polarCoord_target]
      simp_rw [Complex.norm_polarCoord_symm, smul_eq_mul]
    _ = (∫ x in Ioi (0 : Real), x * |x| ^ q * rexp (-|x| ^ p)) * ∫ _ in Ioo (-π) π, 1 := by
      rw [← setIntegral_prod_mul]; rw [volume_eq_prod]
      simp_rw [mul_one]
      congr! 2; ring
    _ = 2 * π * ∫ x in Ioi (0 : Real), x * |x| ^ q * rexp (-|x| ^ p) := by
      simp_rw [integral_const, measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter,
        volume_real_Ioo_of_le (a := -π) (b := π) (by linarith [pi_nonneg]),
        sub_neg_eq_add, ← two_mul, smul_eq_mul, mul_one, mul_comm]
    _ = 2 * π * ∫ x in Ioi (0 : Real), x ^ (q + 1) * rexp (-x ^ p) := by
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [mem_Ioi] at hx
      rw [abs_eq_self.mpr hx.le]; rw [rpow_add hx]; rw [rpow_one]
      ring
    _ = (2 * Real.pi / p) * Real.Gamma ((q + 2) / p) := by
      rw [_root_.integral_rpow_mul_exp_neg_rpow (by linarith) (by linarith)]; rw [add_assoc]; rw [one_add_one_eq_two]
      ring

/--
theorem `Complex.integral_rpow_mul_exp_neg_mul_rpow` / 定理 `Complex.integral_rpow_mul_exp_neg_mul_rpow`

English:
theorem Complex.integral_rpow_mul_exp_neg_mul_rpow
  statement: {p q b : Real} (hp : 1 <= p) (hq : -2 < q)
  proof: by
  calc
    _ = ∫ x in Ioi (0 : Real) ×ˢ Ioo (-π) π, x.1 * (|x.1| ^ q * rexp (-b * |x.1| ^ p)) := by
      rw [← Complex.integral_comp_polarCoord_symm]; rw [polarCoord_target]
      simp_rw [Complex.norm_polarCoord_symm, smul_eq_mul]
    _ = (∫ x in Ioi (0 : Real), x * |x| ^ q * rexp (-b * |x| ^ p)) * ∫ _ in Ioo (-π) π, 1 := by
      rw [← setIntegral_prod_mul]; rw [volume_eq_prod]
      simp_rw [mul_one]
      congr! 2; ring
    _ = 2 * π * ∫ x in Ioi (0 : Real), x * |x| ^ q * rexp (-b * |x| ^ p) := by
      simp_rw [integral_const, measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter,
        volume_real_Ioo_of_le (a := -π) (b := π) (by linarith [pi_nonneg]),
        sub_neg_eq_add, ← two_mul, smul_eq_mul, mul_one, mul_comm]
    _ = 2 * π * ∫ x in Ioi (0 : Real), x ^ (q + 1) * rexp (-b * x ^ p) := by
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [mem_Ioi] at hx
      rw [abs_eq_self.mpr hx.le]; rw [rpow_add hx]; rw [rpow_one]
      ring
    _ = (2 * π / p) * b ^ (-(q + 2) / p) * Real.Gamma ((q + 2) / p) := by
      rw [_root_.integral_rpow_mul_exp_neg_mul_rpow (by linarith) (by linarith) hb]; rw [add_assoc]; rw [one_add_one_eq_two]
      ring

中文:
定理 复形.integral_rpow_mul_exp_neg_mul_rpow
  结论: {p q b : 实数} (hp : 1 <= p) (hq : -2 < q)
  证明: by
  calc
    _ = ∫ x in Ioi (0 : Real) ×ˢ Ioo (-π) π, x.1 * (|x.1| ^ q * rexp (-b * |x.1| ^ p)) := by
      rw [← Complex.integral_comp_polarCoord_symm]; rw [polarCoord_target]
      simp_rw [Complex.norm_polarCoord_symm, smul_eq_mul]
    _ = (∫ x in Ioi (0 : Real), x * |x| ^ q * rexp (-b * |x| ^ p)) * ∫ _ in Ioo (-π) π, 1 := by
      rw [← setIntegral_prod_mul]; rw [volume_eq_prod]
      simp_rw [mul_one]
      congr! 2; ring
    _ = 2 * π * ∫ x in Ioi (0 : Real), x * |x| ^ q * rexp (-b * |x| ^ p) := by
      simp_rw [integral_const, measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter,
        volume_real_Ioo_of_le (a := -π) (b := π) (by linarith [pi_nonneg]),
        sub_neg_eq_add, ← two_mul, smul_eq_mul, mul_one, mul_comm]
    _ = 2 * π * ∫ x in Ioi (0 : Real), x ^ (q + 1) * rexp (-b * x ^ p) := by
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [mem_Ioi] at hx
      rw [abs_eq_self.mpr hx.le]; rw [rpow_add hx]; rw [rpow_one]
      ring
    _ = (2 * π / p) * b ^ (-(q + 2) / p) * Real.Gamma ((q + 2) / p) := by
      rw [_root_.integral_rpow_mul_exp_neg_mul_rpow (by linarith) (by linarith) hb]; rw [add_assoc]; rw [one_add_one_eq_two]
      ring

Depends on / 依赖: Complex.integral_comp_polarCoord_symm, Complex.norm_polarCoord_symm, integral_comp_polarCoord_symm, integral_const, measureR, mul_one, norm_polarCoord_symm, polarCoord_target, setIntegral_prod_mul, simp_rw, smul_eq_mul, volume_eq_prod
-/
theorem Complex.integral_rpow_mul_exp_neg_mul_rpow {p q b : Real} (hp : 1 <= p) (hq : -2 < q)
    (hb : 0 < b) :
    ∫ x : Complex, ‖x‖ ^ q * rexp (-b * ‖x‖ ^ p) = (2 * π / p) *
      b ^ (-(q + 2) / p) * Real.Gamma ((q + 2) / p) := by
  calc
    _ = ∫ x in Ioi (0 : Real) ×ˢ Ioo (-π) π, x.1 * (|x.1| ^ q * rexp (-b * |x.1| ^ p)) := by
      rw [← Complex.integral_comp_polarCoord_symm]; rw [polarCoord_target]
      simp_rw [Complex.norm_polarCoord_symm, smul_eq_mul]
    _ = (∫ x in Ioi (0 : Real), x * |x| ^ q * rexp (-b * |x| ^ p)) * ∫ _ in Ioo (-π) π, 1 := by
      rw [← setIntegral_prod_mul]; rw [volume_eq_prod]
      simp_rw [mul_one]
      congr! 2; ring
    _ = 2 * π * ∫ x in Ioi (0 : Real), x * |x| ^ q * rexp (-b * |x| ^ p) := by
      simp_rw [integral_const, measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter,
        volume_real_Ioo_of_le (a := -π) (b := π) (by linarith [pi_nonneg]),
        sub_neg_eq_add, ← two_mul, smul_eq_mul, mul_one, mul_comm]
    _ = 2 * π * ∫ x in Ioi (0 : Real), x ^ (q + 1) * rexp (-b * x ^ p) := by
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [mem_Ioi] at hx
      rw [abs_eq_self.mpr hx.le]; rw [rpow_add hx]; rw [rpow_one]
      ring
    _ = (2 * π / p) * b ^ (-(q + 2) / p) * Real.Gamma ((q + 2) / p) := by
      rw [_root_.integral_rpow_mul_exp_neg_mul_rpow (by linarith) (by linarith) hb]; rw [add_assoc]; rw [one_add_one_eq_two]
      ring

/--
theorem `Complex.integral_exp_neg_rpow` / 定理 `Complex.integral_exp_neg_rpow`

English:
theorem Complex.integral_exp_neg_rpow
  given: {p : Real} (hp : 1 <= p)
  proof: by
  convert! (integral_rpow_mul_exp_neg_rpow hp (by linarith : (-2 : Real) < 0)) using 1
  · simp_rw [rpow_zero, one_mul]
  · rw [zero_add, Real.Gamma_add_one (div_ne_zero two_ne_zero (by linarith))]
    ring

中文:
定理 复形.integral_exp_neg_rpow
  条件: {p : 实数} (hp : 1 <= p)
  证明: by
  convert! (integral_rpow_mul_exp_neg_rpow hp (by linarith : (-2 : Real) < 0)) using 1
  · simp_rw [rpow_zero, one_mul]
  · rw [zero_add, Real.Gamma_add_one (div_ne_zero two_ne_zero (by linarith))]
    ring

Depends on / 依赖: Gamma_add_one, Real.Gamma_add_one, convert, div_ne_zero, integral_rpow_mul_exp_neg_rpow, one_mul, rpow_zero, simp_rw, two_ne_zero, zero_add
-/
theorem Complex.integral_exp_neg_rpow {p : Real} (hp : 1 <= p) :
    ∫ x : Complex, rexp (-‖x‖ ^ p) = π * Real.Gamma (2 / p + 1) := by
  convert! (integral_rpow_mul_exp_neg_rpow hp (by linarith : (-2 : Real) < 0)) using 1
  · simp_rw [rpow_zero, one_mul]
  · rw [zero_add, Real.Gamma_add_one (div_ne_zero two_ne_zero (by linarith))]
    ring

/--
theorem `Complex.integral_exp_neg_mul_rpow` / 定理 `Complex.integral_exp_neg_mul_rpow`

English:
theorem Complex.integral_exp_neg_mul_rpow
  given: {p b : Real} (hp : 1 <= p) (hb : 0 < b)
  proof: by
  convert! (integral_rpow_mul_exp_neg_mul_rpow hp (by linarith : (-2 : Real) < 0)) hb using 1
  · simp_rw [rpow_zero, one_mul]
  · rw [zero_add, Real.Gamma_add_one (div_ne_zero two_ne_zero (by linarith))]
    ring

中文:
定理 复形.integral_exp_neg_mul_rpow
  条件: {p b : 实数} (hp : 1 <= p) (hb : 0 < b)
  证明: by
  convert! (integral_rpow_mul_exp_neg_mul_rpow hp (by linarith : (-2 : Real) < 0)) hb using 1
  · simp_rw [rpow_zero, one_mul]
  · rw [zero_add, Real.Gamma_add_one (div_ne_zero two_ne_zero (by linarith))]
    ring

Depends on / 依赖: Gamma_add_one, Real.Gamma_add_one, convert, div_ne_zero, integral_rpow_mul_exp_neg_mul_rpow, one_mul, rpow_zero, simp_rw, two_ne_zero, zero_add
-/
theorem Complex.integral_exp_neg_mul_rpow {p b : Real} (hp : 1 <= p) (hb : 0 < b) :
    ∫ x : Complex, rexp (-b * ‖x‖ ^ p) = π * b ^ (-2 / p) * Real.Gamma (2 / p + 1) := by
  convert! (integral_rpow_mul_exp_neg_mul_rpow hp (by linarith : (-2 : Real) < 0)) hb using 1
  · simp_rw [rpow_zero, one_mul]
  · rw [zero_add, Real.Gamma_add_one (div_ne_zero two_ne_zero (by linarith))]
    ring

end complex
