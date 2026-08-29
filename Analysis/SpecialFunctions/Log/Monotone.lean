/-
Copyright (c) 2021 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Logarithm Tonality

In this file we describe the tonality of the logarithm function when multiplied by functions of the
form `x ^ a`.

## Tags

logarithm, tonality
-/

public section


open Set Filter Function

open Topology

noncomputable section

namespace Real

/--
theorem `mul_log_strictMonoOn` / 定理 `mul_log_strictMonoOn`

English:
theorem mul_log_strictMonoOn
  statement: StrictMonoOn (fun x => x * log x) .Ici exp (-1)
  proof: by
  refine strictMonoOn_of_deriv_pos (convex_Ici _) continuous_mul_log.continuousOn fun x hx => ?_
  have hlt : rexp (-1) < x := by simpa using hx
  have hpos : 0 < x := by grind [Real.exp_pos]
  grind [deriv_mul_log, Real.lt_log_iff_exp_lt hpos |>.mpr hlt]

@[deprecated Real.mul_log_strictMonoOn (

中文:
定理 mul_log_strictMonoOn
  结论: StrictMonoOn (fun x => x * log x) .左闭右无界区间 exp (-1)
  证明: by
  refine strictMonoOn_of_deriv_pos (convex_Ici _) continuous_mul_log.continuousOn fun x hx => ?_
  have hlt : rexp (-1) < x := by simpa using hx
  have hpos : 0 < x := by grind [Real.exp_pos]
  grind [deriv_mul_log, Real.lt_log_iff_exp_lt hpos |>.mpr hlt]

@[deprecated Real.mul_log_strictMonoOn (

Depends on / 依赖: Real.exp_pos, Real.lt_log_iff_exp_lt, continuousOn, continuous_mul_log, continuous_mul_log.continuousOn, convex_Ici, deriv_mul_log, exp_pos, lt_log_iff_exp_lt, strictMonoOn_of_deriv_pos
-/
theorem mul_log_strictMonoOn : StrictMonoOn (fun x => x * log x) .Ici exp (-1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici _) continuous_mul_log.continuousOn fun x hx => ?_
  have hlt : rexp (-1) < x := by simpa using hx
  have hpos : 0 < x := by grind [Real.exp_pos]
  grind [deriv_mul_log, Real.lt_log_iff_exp_lt hpos |>.mpr hlt]

@[deprecated Real.mul_log_strictMonoOn (since := "2026-04-07")]
/--
theorem `log_mul_self_monotoneOn` / 定理 `log_mul_self_monotoneOn`

English:
theorem log_mul_self_monotoneOn
  statement: MonotoneOn (fun x : Real => log x * x) { x | 1 <= x }
  proof: by
  grind [mul_log_strictMonoOn.monotoneOn, MonotoneOn.mono, show exp (-1) < 1 by norm_num]

中文:
定理 log_mul_self_monotoneOn
  结论: MonotoneOn (fun x : 实数 => log x * x) { x | 1 <= x }
  证明: by
  grind [mul_log_strictMonoOn.monotoneOn, MonotoneOn.mono, show exp (-1) < 1 by norm_num]

Depends on / 依赖: MonotoneOn, MonotoneOn.mono, monotoneOn, mul_log_strictMonoOn, mul_log_strictMonoOn.monotoneOn
-/
theorem log_mul_self_monotoneOn : MonotoneOn (fun x : Real => log x * x) { x | 1 <= x } := by
  grind [mul_log_strictMonoOn.monotoneOn, MonotoneOn.mono, show exp (-1) < 1 by norm_num]

/--
theorem `mul_log_strictAntiOn` / 定理 `mul_log_strictAntiOn`

English:
theorem mul_log_strictAntiOn
  proof: by
  refine strictAntiOn_of_deriv_neg (convex_Icc ..) continuous_mul_log.continuousOn fun x hx => ?_
  have hgt : x < rexp (-1) := by simp_all [interior_Icc, mem_Ioo]
  have hpos : 0 < x := by simp_all [interior_Icc, mem_Ioo]
  grind [deriv_mul_log, Real.log_lt_iff_lt_exp hpos |>.mpr hgt]

中文:
定理 mul_log_strictAntiOn
  证明: by
  refine strictAntiOn_of_deriv_neg (convex_Icc ..) continuous_mul_log.continuousOn fun x hx => ?_
  have hgt : x < rexp (-1) := by simp_all [interior_Icc, mem_Ioo]
  have hpos : 0 < x := by simp_all [interior_Icc, mem_Ioo]
  grind [deriv_mul_log, Real.log_lt_iff_lt_exp hpos |>.mpr hgt]

Depends on / 依赖: Real.log_lt_iff_lt_exp, continuousOn, continuous_mul_log, continuous_mul_log.continuousOn, convex_Icc, deriv_mul_log, interior_Icc, log_lt_iff_lt_exp, mem_Ioo, strictAntiOn_of_deriv_neg
-/
theorem mul_log_strictAntiOn :
StrictAntiOn (fun x : Real => x * log x) .Icc 0 (exp (-1)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc ..) continuous_mul_log.continuousOn fun x hx => ?_
  have hgt : x < rexp (-1) := by simp_all [interior_Icc, mem_Ioo]
  have hpos : 0 < x := by simp_all [interior_Icc, mem_Ioo]
  grind [deriv_mul_log, Real.log_lt_iff_lt_exp hpos |>.mpr hgt]

/--
theorem `log_div_self_antitoneOn` / 定理 `log_div_self_antitoneOn`

English:
theorem log_div_self_antitoneOn
  statement: AntitoneOn (fun x : Real => log x / x) .Ici (exp 1)
  proof: by
  intro x hex y hey hxy
  have x_pos : 0 < x := (exp_pos 1).trans_le hex
  have y_pos : 0 < y := (exp_pos 1).trans_le hey
  have hlogx : 1 <= log x := by rwa [le_log_iff_exp_le x_pos]
  have hyx : 0 <= y / x - 1 := by rwa [le_sub_iff_add_le, le_div_iff₀ x_pos, zero_add, one_mul]
  rw [div_le_iff₀

中文:
定理 log_div_self_antitoneOn
  结论: AntitoneOn (fun x : 实数 => log x / x) .左闭右无界区间 (exp 1)
  证明: by
  intro x hex y hey hxy
  have x_pos : 0 < x := (exp_pos 1).trans_le hex
  have y_pos : 0 < y := (exp_pos 1).trans_le hey
  have hlogx : 1 <= log x := by rwa [le_log_iff_exp_le x_pos]
  have hyx : 0 <= y / x - 1 := by rwa [le_sub_iff_add_le, le_div_iff₀ x_pos, zero_add, one_mul]
  rw [div_le_iff₀

Depends on / 依赖: div_pos, exp_pos, le_log_iff_exp_le, le_mu, le_sub_iff_add_le, log_div, log_le_sub_one_of_pos, one_mul, sub_le_sub_iff_right, trans_le, x_pos, x_pos.ne, y_pos, y_pos.ne, zero_add
-/
theorem log_div_self_antitoneOn : AntitoneOn (fun x : Real => log x / x) .Ici (exp 1) := by
  intro x hex y hey hxy
  have x_pos : 0 < x := (exp_pos 1).trans_le hex
  have y_pos : 0 < y := (exp_pos 1).trans_le hey
  have hlogx : 1 <= log x := by rwa [le_log_iff_exp_le x_pos]
  have hyx : 0 <= y / x - 1 := by rwa [le_sub_iff_add_le, le_div_iff₀ x_pos, zero_add, one_mul]
  rw [div_le_iff₀ y_pos]; rw [← sub_le_sub_iff_right (log x)]
  calc
    log y - log x = log (y / x) := by rw [log_div y_pos.ne' x_pos.ne']
    _ <= y / x - 1 := log_le_sub_one_of_pos (div_pos y_pos x_pos)
    _ <= log x * (y / x - 1) := le_mul_of_one_le_left hyx hlogx
    _ = log x / x * y - log x := by ring

/--
theorem `log_div_self_rpow_antitoneOn` / 定理 `log_div_self_rpow_antitoneOn`

English:
theorem log_div_self_rpow_antitoneOn
  given: {a : Real} (ha : 0 < a)
  proof: by
  intro x hex y _ hxy
  simp only
  have x_pos : 0 < x := lt_of_lt_of_le (exp_pos a⁻¹) (le_of_le_of_eq hex rfl)
  have y_pos : 0 < y := by linarith
  nth_rw 1 [← rpow_one y, ← rpow_one x]
  rw [← div_self (ne_of_lt ha).symm]; rw [div_eq_mul_one_div a a]; rw [rpow_mul y_pos.le]; rw [rpow_mul x_pos

中文:
定理 log_div_self_rpow_antitoneOn
  条件: {a : 实数} (ha : 0 < a)
  证明: by
  intro x hex y _ hxy
  simp only
  have x_pos : 0 < x := lt_of_lt_of_le (exp_pos a⁻¹) (le_of_le_of_eq hex rfl)
  have y_pos : 0 < y := by linarith
  nth_rw 1 [← rpow_one y, ← rpow_one x]
  rw [← div_self (ne_of_lt ha).symm]; rw [div_eq_mul_one_div a a]; rw [rpow_mul y_pos.le]; rw [rpow_mul x_pos

Depends on / 依赖: div_eq_mul_one_div, div_self, exp_pos, hbound, le_of_le_of_eq, log_rpow, lt_of_lt_of_le, mul_div_assoc, ne_of_lt, nth_rw, one_div_pos, one_div_pos.mpr, rpow_mul, rpow_one, rpow_pos_of_pos, x_pos, x_pos.le, y_pos, y_pos.le
-/
theorem log_div_self_rpow_antitoneOn {a : Real} (ha : 0 < a) :
AntitoneOn (fun x : Real => log x / x ^ a) .Ici (exp a⁻¹) := by
  intro x hex y _ hxy
  simp only
  have x_pos : 0 < x := lt_of_lt_of_le (exp_pos a⁻¹) (le_of_le_of_eq hex rfl)
  have y_pos : 0 < y := by linarith
  nth_rw 1 [← rpow_one y, ← rpow_one x]
  rw [← div_self (ne_of_lt ha).symm]; rw [div_eq_mul_one_div a a]; rw [rpow_mul y_pos.le]; rw [rpow_mul x_pos.le]; rw [log_rpow (rpow_pos_of_pos y_pos a)]; rw [log_rpow (rpow_pos_of_pos x_pos a)]; rw [mul_div_assoc]; rw [mul_div_assoc]; rw [mul_le_mul_iff_right₀ (one_div_pos.mpr ha)]
  have hbound {z : Real} (hz : z in Ici (rexp a⁻¹)) : z ^ a in {b | rexp 1 <= b} := by
    rw [mem_ofPred_eq]
    convert! rpow_le_rpow _ hz (le_of_lt ha) using 1
    · simp only [← exp_mul, Real.exp_eq_exp, field]
    positivity
  refine log_div_self_antitoneOn (hbound hex) (hbound (hex.trans hxy)) ?_
  gcongr

/--
theorem `log_div_sqrt_antitoneOn` / 定理 `log_div_sqrt_antitoneOn`

English:
theorem log_div_sqrt_antitoneOn
  statement: AntitoneOn (fun x : Real => log x / √x) .Ici (exp 2)
  proof: by
  simp_rw [sqrt_eq_rpow]
  convert! log_div_self_rpow_antitoneOn one_half_pos
  norm_num

中文:
定理 log_div_sqrt_antitoneOn
  结论: AntitoneOn (fun x : 实数 => log x / √x) .左闭右无界区间 (exp 2)
  证明: by
  simp_rw [sqrt_eq_rpow]
  convert! log_div_self_rpow_antitoneOn one_half_pos
  norm_num

Depends on / 依赖: convert, log_div_self_rpow_antitoneOn, one_half_pos, simp_rw, sqrt_eq_rpow
-/
theorem log_div_sqrt_antitoneOn : AntitoneOn (fun x : Real => log x / √x) .Ici (exp 2) := by
  simp_rw [sqrt_eq_rpow]
  convert! log_div_self_rpow_antitoneOn one_half_pos
  norm_num

end Real
