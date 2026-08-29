/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel, Heather Macbeth
-/
module

public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.LinearCombination

/-!
# Collection of convex functions

In this file we prove that the following functions are convex or strictly convex:

* `strictConvexOn_exp` : The exponential function is strictly convex.
* `strictConcaveOn_log_Ioi`, `strictConcaveOn_log_Iio`: `Real.log` is strictly concave on
  $(0, +∞)$ and $(-∞, 0)$ respectively.
* `convexOn_rpow`, `strictConvexOn_rpow` : For `p : ℝ`, `fun x ↦ x ^ p` is convex on $[0, +∞)$ when
  `1 ≤ p` and strictly convex when `1 < p`.

The proofs in this file are deliberately elementary, *not* by appealing to the sign of the second
derivative. This is in order to keep this file early in the import hierarchy, since it is on the
path to Hölder's and Minkowski's inequalities and after that to Lp spaces and most of measure
theory.

(Strict) concavity of `fun x ↦ x ^ p` for `0 < p < 1` (`0 ≤ p ≤ 1`) can be found in
`Mathlib/Analysis/Convex/SpecificFunctions/Pow.lean`.

## See also

`Mathlib/Analysis/Convex/Mul.lean` for convexity of `x ↦ x ^ n`
-/

public section

open Real Set NNReal

/--
theorem `strictConvexOn_exp` / 定理 `strictConvexOn_exp`

English:
theorem strictConvexOn_exp
  statement: StrictConvexOn Real univ exp
  proof: by
  apply strictConvexOn_of_slope_strict_mono_adjacent convex_univ
  rintro x y z - - hxy hyz
  trans exp y
  · have h1 : 0 < y - x := by linarith
    have h2 : x - y < 0 := by linarith
    rw [div_lt_iff₀ h1]
    calc
      exp y - exp x = exp y - exp y * exp (x - y) := by rw [← exp_add]; ring_nf
      _ = exp y * (1 - exp (x - y)) := by ring
      _ < exp y * -(x - y) := by gcongr; linarith [add_one_lt_exp h2.ne]
      _ = exp y * (y - x) := by ring
  · have h1 : 0 < z - y := by linarith
    rw [lt_div_iff₀ h1]
    calc
      exp y * (z - y) < exp y * (exp (z - y) - 1) := by
        gcongr _ * ?_
        linarith [add_one_lt_exp h1.ne']
      _ = exp (z - y) * exp y - exp y := by ring
      _ <= exp z - exp y := by rw [← exp_add]; ring_nf; rfl

中文:
定理 strictConvexOn_exp
  结论: StrictConvexOn 实数 univ exp
  证明: by
  apply strictConvexOn_of_slope_strict_mono_adjacent convex_univ
  rintro x y z - - hxy hyz
  trans exp y
  · have h1 : 0 < y - x := by linarith
    have h2 : x - y < 0 := by linarith
    rw [div_lt_iff₀ h1]
    calc
      exp y - exp x = exp y - exp y * exp (x - y) := by rw [← exp_add]; ring_nf
      _ = exp y * (1 - exp (x - y)) := by ring
      _ < exp y * -(x - y) := by gcongr; linarith [add_one_lt_exp h2.ne]
      _ = exp y * (y - x) := by ring
  · have h1 : 0 < z - y := by linarith
    rw [lt_div_iff₀ h1]
    calc
      exp y * (z - y) < exp y * (exp (z - y) - 1) := by
        gcongr _ * ?_
        linarith [add_one_lt_exp h1.ne']
      _ = exp (z - y) * exp y - exp y := by ring
      _ <= exp z - exp y := by rw [← exp_add]; ring_nf; rfl

Depends on / 依赖: add_one_lt_exp, convex_univ, exp_add, h2.ne, ring_nf, strictConvexOn_of_slope_strict_mono_adjacent
-/
theorem strictConvexOn_exp : StrictConvexOn Real univ exp := by
  apply strictConvexOn_of_slope_strict_mono_adjacent convex_univ
  rintro x y z - - hxy hyz
  trans exp y
  · have h1 : 0 < y - x := by linarith
    have h2 : x - y < 0 := by linarith
    rw [div_lt_iff₀ h1]
    calc
      exp y - exp x = exp y - exp y * exp (x - y) := by rw [← exp_add]; ring_nf
      _ = exp y * (1 - exp (x - y)) := by ring
      _ < exp y * -(x - y) := by gcongr; linarith [add_one_lt_exp h2.ne]
      _ = exp y * (y - x) := by ring
  · have h1 : 0 < z - y := by linarith
    rw [lt_div_iff₀ h1]
    calc
      exp y * (z - y) < exp y * (exp (z - y) - 1) := by
        gcongr _ * ?_
        linarith [add_one_lt_exp h1.ne']
      _ = exp (z - y) * exp y - exp y := by ring
      _ <= exp z - exp y := by rw [← exp_add]; ring_nf; rfl

/--
theorem `convexOn_exp` / 定理 `convexOn_exp`

English:
theorem convexOn_exp
  statement: ConvexOn Real univ exp
  proof: strictConvexOn_exp.convexOn

中文:
定理 convexOn_exp
  结论: ConvexOn 实数 univ exp
  证明: strictConvexOn_exp.convexOn

Depends on / 依赖: convexOn, strictConvexOn_exp, strictConvexOn_exp.convexOn
-/
theorem convexOn_exp : ConvexOn Real univ exp :=
  strictConvexOn_exp.convexOn

/--
theorem `strictConcaveOn_log_Ioi` / 定理 `strictConcaveOn_log_Ioi`

English:
theorem strictConcaveOn_log_Ioi
  statement: StrictConcaveOn Real (Ioi 0) log
  proof: by
  apply strictConcaveOn_of_slope_strict_anti_adjacent (convex_Ioi (0 : Real))
  intro x y z (hx : 0 < x) (hz : 0 < z) hxy hyz
  have hy : 0 < y := hx.trans hxy
  trans y⁻¹
  · have h : 0 < z - y := by linarith
    rw [div_lt_iff₀ h]
    have hyz' : 0 < z / y := by positivity
    have hyz'' : z / y != 1 := by
      contrapose! h
      rw [div_eq_one_iff_eq hy.ne'] at h
      simp [h]
    calc
      log z - log y = log (z / y) := by rw [← log_div hz.ne' hy.ne']
      _ < z / y - 1 := log_lt_sub_one_of_pos hyz' hyz''
      _ = y⁻¹ * (z - y) := by field
  · have h : 0 < y - x := by linarith
    rw [lt_div_iff₀ h]
    have hxy' : 0 < x / y := by positivity
    have hxy'' : x / y != 1 := by
      contrapose! h
      rw [div_eq_one_iff_eq hy.ne'] at h
      simp [h]
    calc
      y⁻¹ * (y - x) = 1 - x / y := by field
      _ < -log (x / y) := by linarith [log_lt_sub_one_of_pos hxy' hxy'']
      _ = -(log x - log y) := by rw [log_div hx.ne' hy.ne']
      _ = log y - log x := by ring

中文:
定理 strictConcaveOn_log_Ioi
  结论: StrictConcaveOn 实数 (左开右无界区间 0) log
  证明: by
  apply strictConcaveOn_of_slope_strict_anti_adjacent (convex_Ioi (0 : Real))
  intro x y z (hx : 0 < x) (hz : 0 < z) hxy hyz
  have hy : 0 < y := hx.trans hxy
  trans y⁻¹
  · have h : 0 < z - y := by linarith
    rw [div_lt_iff₀ h]
    have hyz' : 0 < z / y := by positivity
    have hyz'' : z / y != 1 := by
      contrapose! h
      rw [div_eq_one_iff_eq hy.ne'] at h
      simp [h]
    calc
      log z - log y = log (z / y) := by rw [← log_div hz.ne' hy.ne']
      _ < z / y - 1 := log_lt_sub_one_of_pos hyz' hyz''
      _ = y⁻¹ * (z - y) := by field
  · have h : 0 < y - x := by linarith
    rw [lt_div_iff₀ h]
    have hxy' : 0 < x / y := by positivity
    have hxy'' : x / y != 1 := by
      contrapose! h
      rw [div_eq_one_iff_eq hy.ne'] at h
      simp [h]
    calc
      y⁻¹ * (y - x) = 1 - x / y := by field
      _ < -log (x / y) := by linarith [log_lt_sub_one_of_pos hxy' hxy'']
      _ = -(log x - log y) := by rw [log_div hx.ne' hy.ne']
      _ = log y - log x := by ring

Depends on / 依赖: contrapose, convex_Ioi, div_eq_one_iff_eq, hx.trans, hy.ne, hz.ne, log_div, log_lt_sub_one_of_pos, strictConcaveOn_of_slope_strict_anti_adjacent
-/
theorem strictConcaveOn_log_Ioi : StrictConcaveOn Real (Ioi 0) log := by
  apply strictConcaveOn_of_slope_strict_anti_adjacent (convex_Ioi (0 : Real))
  intro x y z (hx : 0 < x) (hz : 0 < z) hxy hyz
  have hy : 0 < y := hx.trans hxy
  trans y⁻¹
  · have h : 0 < z - y := by linarith
    rw [div_lt_iff₀ h]
    have hyz' : 0 < z / y := by positivity
    have hyz'' : z / y != 1 := by
      contrapose! h
      rw [div_eq_one_iff_eq hy.ne'] at h
      simp [h]
    calc
      log z - log y = log (z / y) := by rw [← log_div hz.ne' hy.ne']
      _ < z / y - 1 := log_lt_sub_one_of_pos hyz' hyz''
      _ = y⁻¹ * (z - y) := by field
  · have h : 0 < y - x := by linarith
    rw [lt_div_iff₀ h]
    have hxy' : 0 < x / y := by positivity
    have hxy'' : x / y != 1 := by
      contrapose! h
      rw [div_eq_one_iff_eq hy.ne'] at h
      simp [h]
    calc
      y⁻¹ * (y - x) = 1 - x / y := by field
      _ < -log (x / y) := by linarith [log_lt_sub_one_of_pos hxy' hxy'']
      _ = -(log x - log y) := by rw [log_div hx.ne' hy.ne']
      _ = log y - log x := by ring

/--
theorem `one_add_mul_self_lt_rpow_one_add` / 定理 `one_add_mul_self_lt_rpow_one_add`

English:
theorem one_add_mul_self_lt_rpow_one_add
  given: {s : Real} (hs : -1 <= s) (hs' : s != 0) {p : Real} (hp : 1 < p)
  proof: by
  have hp' : 0 < p := zero_lt_one.trans hp
  rcases eq_or_lt_of_le hs with rfl | hs
  · rwa [add_neg_cancel, zero_rpow hp'.ne', mul_neg_one, add_neg_lt_iff_lt_add, zero_add]
  have hs1 : 0 < 1 + s := neg_lt_iff_pos_add'.mp hs
  rcases le_or_gt (1 + p * s) 0 with hs2 | hs2
  · exact hs2.trans_lt (rpow_pos_of_pos hs1 _)
  have hs3 : 1 + s != 1 := hs' ∘ add_eq_left.mp
  have hs4 : 1 + p * s != 1 := by
    contrapose hs'; rwa [add_eq_left, mul_eq_zero, eq_false_intro hp'.ne', false_or] at hs'
  rw [rpow_def_of_pos hs1]; rw [← exp_log hs2]
  apply exp_strictMono
  rcases lt_or_gt_of_ne hs' with hs' | hs'
  · rw [← div_lt_iff₀ hp', ← div_lt_div_right_of_neg hs']
    convert! strictConcaveOn_log_Ioi.secant_strict_mono (zero_lt_one' Real) hs2 hs1 hs4 hs3 _ using 1
    · rw [add_sub_cancel_left, log_one, sub_zero]
    · rw [add_sub_cancel_left, div_div, log_one, sub_zero]
    · gcongr
      exact mul_lt_of_one_lt_left hs' hp
  · rw [← div_lt_iff₀ hp', ← div_lt_div_iff_of_pos_right hs']
    convert! strictConcaveOn_log_Ioi.secant_strict_mono (zero_lt_one' Real) hs1 hs2 hs3 hs4 _ using 1
    · rw [add_sub_cancel_left, div_div, log_one, sub_zero]
    · rw [add_sub_cancel_left, log_one, sub_zero]
    · gcongr
      exact lt_mul_of_one_lt_left hs' hp

中文:
定理 one_add_mul_self_lt_rpow_one_add
  条件: {s : 实数} (hs : -1 <= s) (hs' : s != 0) {p : 实数} (hp : 1 < p)
  证明: by
  have hp' : 0 < p := zero_lt_one.trans hp
  rcases eq_or_lt_of_le hs with rfl | hs
  · rwa [add_neg_cancel, zero_rpow hp'.ne', mul_neg_one, add_neg_lt_iff_lt_add, zero_add]
  have hs1 : 0 < 1 + s := neg_lt_iff_pos_add'.mp hs
  rcases le_or_gt (1 + p * s) 0 with hs2 | hs2
  · exact hs2.trans_lt (rpow_pos_of_pos hs1 _)
  have hs3 : 1 + s != 1 := hs' ∘ add_eq_left.mp
  have hs4 : 1 + p * s != 1 := by
    contrapose hs'; rwa [add_eq_left, mul_eq_zero, eq_false_intro hp'.ne', false_or] at hs'
  rw [rpow_def_of_pos hs1]; rw [← exp_log hs2]
  apply exp_strictMono
  rcases lt_or_gt_of_ne hs' with hs' | hs'
  · rw [← div_lt_iff₀ hp', ← div_lt_div_right_of_neg hs']
    convert! strictConcaveOn_log_Ioi.secant_strict_mono (zero_lt_one' Real) hs2 hs1 hs4 hs3 _ using 1
    · rw [add_sub_cancel_left, log_one, sub_zero]
    · rw [add_sub_cancel_left, div_div, log_one, sub_zero]
    · gcongr
      exact mul_lt_of_one_lt_left hs' hp
  · rw [← div_lt_iff₀ hp', ← div_lt_div_iff_of_pos_right hs']
    convert! strictConcaveOn_log_Ioi.secant_strict_mono (zero_lt_one' Real) hs1 hs2 hs3 hs4 _ using 1
    · rw [add_sub_cancel_left, div_div, log_one, sub_zero]
    · rw [add_sub_cancel_left, log_one, sub_zero]
    · gcongr
      exact lt_mul_of_one_lt_left hs' hp

Depends on / 依赖: add_eq_left, add_eq_left.mp, add_neg_cancel, add_neg_lt_iff_lt_add, contrapose, eq_false_intro, eq_or_lt_of_le, false_or, hs2.trans_lt, le_or_gt, mul_eq_zero, mul_neg_one, neg_lt_iff_pos_add, rpow_def_of_pos, rpow_pos_of_pos, trans_lt, zero_add, zero_lt_one, zero_lt_one.trans, zero_rpow
-/
theorem one_add_mul_self_lt_rpow_one_add {s : Real} (hs : -1 <= s) (hs' : s != 0) {p : Real} (hp : 1 < p) :
    1 + p * s < (1 + s) ^ p := by
  have hp' : 0 < p := zero_lt_one.trans hp
  rcases eq_or_lt_of_le hs with rfl | hs
  · rwa [add_neg_cancel, zero_rpow hp'.ne', mul_neg_one, add_neg_lt_iff_lt_add, zero_add]
  have hs1 : 0 < 1 + s := neg_lt_iff_pos_add'.mp hs
  rcases le_or_gt (1 + p * s) 0 with hs2 | hs2
  · exact hs2.trans_lt (rpow_pos_of_pos hs1 _)
  have hs3 : 1 + s != 1 := hs' ∘ add_eq_left.mp
  have hs4 : 1 + p * s != 1 := by
    contrapose hs'; rwa [add_eq_left, mul_eq_zero, eq_false_intro hp'.ne', false_or] at hs'
  rw [rpow_def_of_pos hs1]; rw [← exp_log hs2]
  apply exp_strictMono
  rcases lt_or_gt_of_ne hs' with hs' | hs'
  · rw [← div_lt_iff₀ hp', ← div_lt_div_right_of_neg hs']
    convert! strictConcaveOn_log_Ioi.secant_strict_mono (zero_lt_one' Real) hs2 hs1 hs4 hs3 _ using 1
    · rw [add_sub_cancel_left, log_one, sub_zero]
    · rw [add_sub_cancel_left, div_div, log_one, sub_zero]
    · gcongr
      exact mul_lt_of_one_lt_left hs' hp
  · rw [← div_lt_iff₀ hp', ← div_lt_div_iff_of_pos_right hs']
    convert! strictConcaveOn_log_Ioi.secant_strict_mono (zero_lt_one' Real) hs1 hs2 hs3 hs4 _ using 1
    · rw [add_sub_cancel_left, div_div, log_one, sub_zero]
    · rw [add_sub_cancel_left, log_one, sub_zero]
    · gcongr
      exact lt_mul_of_one_lt_left hs' hp

/--
theorem `one_add_mul_self_le_rpow_one_add` / 定理 `one_add_mul_self_le_rpow_one_add`

English:
theorem one_add_mul_self_le_rpow_one_add
  given: {s : Real} (hs : -1 <= s) {p : Real} (hp : 1 <= p)
  proof: by
  rcases eq_or_lt_of_le hp with (rfl | hp)
  · simp
  by_cases hs' : s = 0
  · simp [hs']
  exact (one_add_mul_self_lt_rpow_one_add hs hs' hp).le

中文:
定理 one_add_mul_self_le_rpow_one_add
  条件: {s : 实数} (hs : -1 <= s) {p : 实数} (hp : 1 <= p)
  证明: by
  rcases eq_or_lt_of_le hp with (rfl | hp)
  · simp
  by_cases hs' : s = 0
  · simp [hs']
  exact (one_add_mul_self_lt_rpow_one_add hs hs' hp).le

Depends on / 依赖: eq_or_lt_of_le, one_add_mul_self_lt_rpow_one_add
-/
theorem one_add_mul_self_le_rpow_one_add {s : Real} (hs : -1 <= s) {p : Real} (hp : 1 <= p) :
    1 + p * s <= (1 + s) ^ p := by
  rcases eq_or_lt_of_le hp with (rfl | hp)
  · simp
  by_cases hs' : s = 0
  · simp [hs']
  exact (one_add_mul_self_lt_rpow_one_add hs hs' hp).le

/--
theorem `rpow_one_add_lt_one_add_mul_self` / 定理 `rpow_one_add_lt_one_add_mul_self`

English:
theorem rpow_one_add_lt_one_add_mul_self
  statement: {s : Real} (hs : -1 <= s) (hs' : s != 0) {p : Real} (hp1 : 0 < p)
  proof: by
  rcases eq_or_lt_of_le hs with rfl | hs
  · rwa [add_neg_cancel, zero_rpow hp1.ne', mul_neg_one, lt_add_neg_iff_add_lt, zero_add]
  have hs1 : 0 < 1 + s := neg_lt_iff_pos_add'.mp hs
  have hs2 : 0 < 1 + p * s := by
    rw [← neg_lt_iff_pos_add']
    rcases lt_or_gt_of_ne hs' with h | h
    · exact hs.trans (lt_mul_of_lt_one_left h hp2)
    · exact neg_one_lt_zero.trans (mul_pos hp1 h)
  have hs3 : 1 + s != 1 := hs' ∘ add_eq_left.mp
  have hs4 : 1 + p * s != 1 := by
    contrapose hs'; rwa [add_eq_left, mul_eq_zero, eq_false_intro hp1.ne', false_or] at hs'
  rw [rpow_def_of_pos hs1]; rw [← exp_log hs2]
  apply exp_strictMono
  rcases lt_or_gt_of_ne hs' with hs' | hs'
  · rw [← lt_div_iff₀ hp1, ← div_lt_div_right_of_neg hs']
    convert! strictConcaveOn_log_Ioi.secant_strict_mono (zero_lt_one' Real) hs1 hs2 hs3 hs4 _ using 1
    · rw [add_sub_cancel_left, div_div, log_one, sub_zero]
    · rw [add_sub_cancel_left, log_one, sub_zero]
    · gcongr
      exact lt_mul_of_lt_one_left hs' hp2
  · rw [← lt_div_iff₀ hp1, ← div_lt_div_iff_of_pos_right hs']
    convert! strictConcaveOn_log_Ioi.secant_strict_mono (zero_lt_one' Real) hs2 hs1 hs4 hs3 _ using 1
    · rw [add_sub_cancel_left, log_one, sub_zero]
    · rw [add_sub_cancel_left, div_div, log_one, sub_zero]
    · gcongr
      exact mul_lt_of_lt_one_left hs' hp2

中文:
定理 rpow_one_add_lt_one_add_mul_self
  结论: {s : 实数} (hs : -1 <= s) (hs' : s != 0) {p : 实数} (hp1 : 0 < p)
  证明: by
  rcases eq_or_lt_of_le hs with rfl | hs
  · rwa [add_neg_cancel, zero_rpow hp1.ne', mul_neg_one, lt_add_neg_iff_add_lt, zero_add]
  have hs1 : 0 < 1 + s := neg_lt_iff_pos_add'.mp hs
  have hs2 : 0 < 1 + p * s := by
    rw [← neg_lt_iff_pos_add']
    rcases lt_or_gt_of_ne hs' with h | h
    · exact hs.trans (lt_mul_of_lt_one_left h hp2)
    · exact neg_one_lt_zero.trans (mul_pos hp1 h)
  have hs3 : 1 + s != 1 := hs' ∘ add_eq_left.mp
  have hs4 : 1 + p * s != 1 := by
    contrapose hs'; rwa [add_eq_left, mul_eq_zero, eq_false_intro hp1.ne', false_or] at hs'
  rw [rpow_def_of_pos hs1]; rw [← exp_log hs2]
  apply exp_strictMono
  rcases lt_or_gt_of_ne hs' with hs' | hs'
  · rw [← lt_div_iff₀ hp1, ← div_lt_div_right_of_neg hs']
    convert! strictConcaveOn_log_Ioi.secant_strict_mono (zero_lt_one' Real) hs1 hs2 hs3 hs4 _ using 1
    · rw [add_sub_cancel_left, div_div, log_one, sub_zero]
    · rw [add_sub_cancel_left, log_one, sub_zero]
    · gcongr
      exact lt_mul_of_lt_one_left hs' hp2
  · rw [← lt_div_iff₀ hp1, ← div_lt_div_iff_of_pos_right hs']
    convert! strictConcaveOn_log_Ioi.secant_strict_mono (zero_lt_one' Real) hs2 hs1 hs4 hs3 _ using 1
    · rw [add_sub_cancel_left, log_one, sub_zero]
    · rw [add_sub_cancel_left, div_div, log_one, sub_zero]
    · gcongr
      exact mul_lt_of_lt_one_left hs' hp2

Depends on / 依赖: add_eq_left, add_eq_left.mp, add_neg_cancel, contrapose, eq_fals, eq_or_lt_of_le, hp1.ne, hs.trans, lt_add_neg_iff_add_lt, lt_mul_of_lt_one_left, lt_or_gt_of_ne, mul_eq_zero, mul_neg_one, mul_pos, neg_lt_iff_pos_add, neg_one_lt_zero, neg_one_lt_zero.trans, zero_add, zero_rpow
-/
theorem rpow_one_add_lt_one_add_mul_self {s : Real} (hs : -1 <= s) (hs' : s != 0) {p : Real} (hp1 : 0 < p)
    (hp2 : p < 1) : (1 + s) ^ p < 1 + p * s := by
  rcases eq_or_lt_of_le hs with rfl | hs
  · rwa [add_neg_cancel, zero_rpow hp1.ne', mul_neg_one, lt_add_neg_iff_add_lt, zero_add]
  have hs1 : 0 < 1 + s := neg_lt_iff_pos_add'.mp hs
  have hs2 : 0 < 1 + p * s := by
    rw [← neg_lt_iff_pos_add']
    rcases lt_or_gt_of_ne hs' with h | h
    · exact hs.trans (lt_mul_of_lt_one_left h hp2)
    · exact neg_one_lt_zero.trans (mul_pos hp1 h)
  have hs3 : 1 + s != 1 := hs' ∘ add_eq_left.mp
  have hs4 : 1 + p * s != 1 := by
    contrapose hs'; rwa [add_eq_left, mul_eq_zero, eq_false_intro hp1.ne', false_or] at hs'
  rw [rpow_def_of_pos hs1]; rw [← exp_log hs2]
  apply exp_strictMono
  rcases lt_or_gt_of_ne hs' with hs' | hs'
  · rw [← lt_div_iff₀ hp1, ← div_lt_div_right_of_neg hs']
    convert! strictConcaveOn_log_Ioi.secant_strict_mono (zero_lt_one' Real) hs1 hs2 hs3 hs4 _ using 1
    · rw [add_sub_cancel_left, div_div, log_one, sub_zero]
    · rw [add_sub_cancel_left, log_one, sub_zero]
    · gcongr
      exact lt_mul_of_lt_one_left hs' hp2
  · rw [← lt_div_iff₀ hp1, ← div_lt_div_iff_of_pos_right hs']
    convert! strictConcaveOn_log_Ioi.secant_strict_mono (zero_lt_one' Real) hs2 hs1 hs4 hs3 _ using 1
    · rw [add_sub_cancel_left, log_one, sub_zero]
    · rw [add_sub_cancel_left, div_div, log_one, sub_zero]
    · gcongr
      exact mul_lt_of_lt_one_left hs' hp2

/--
theorem `rpow_one_add_le_one_add_mul_self` / 定理 `rpow_one_add_le_one_add_mul_self`

English:
theorem rpow_one_add_le_one_add_mul_self
  given: {s : Real} (hs : -1 <= s) {p : Real} (hp1 : 0 <= p) (hp2 : p <= 1)
  proof: by
  rcases eq_or_lt_of_le hp1 with (rfl | hp1)
  · simp
  rcases eq_or_lt_of_le hp2 with (rfl | hp2)
  · simp
  by_cases hs' : s = 0
  · simp [hs']
  exact (rpow_one_add_lt_one_add_mul_self hs hs' hp1 hp2).le

中文:
定理 rpow_one_add_le_one_add_mul_self
  条件: {s : 实数} (hs : -1 <= s) {p : 实数} (hp1 : 0 <= p) (hp2 : p <= 1)
  证明: by
  rcases eq_or_lt_of_le hp1 with (rfl | hp1)
  · simp
  rcases eq_or_lt_of_le hp2 with (rfl | hp2)
  · simp
  by_cases hs' : s = 0
  · simp [hs']
  exact (rpow_one_add_lt_one_add_mul_self hs hs' hp1 hp2).le

Depends on / 依赖: eq_or_lt_of_le, rpow_one_add_lt_one_add_mul_self
-/
theorem rpow_one_add_le_one_add_mul_self {s : Real} (hs : -1 <= s) {p : Real} (hp1 : 0 <= p) (hp2 : p <= 1) :
    (1 + s) ^ p <= 1 + p * s := by
  rcases eq_or_lt_of_le hp1 with (rfl | hp1)
  · simp
  rcases eq_or_lt_of_le hp2 with (rfl | hp2)
  · simp
  by_cases hs' : s = 0
  · simp [hs']
  exact (rpow_one_add_lt_one_add_mul_self hs hs' hp1 hp2).le

/--
theorem `strictConvexOn_rpow` / 定理 `strictConvexOn_rpow`

English:
theorem strictConvexOn_rpow
  given: {p : Real} (hp : 1 < p)
  statement: StrictConvexOn Real (Ici 0) fun x : Real => x ^ p
  proof: by
  apply strictConvexOn_of_slope_strict_mono_adjacent (convex_Ici (0 : Real))
  intro x y z (hx : 0 <= x) (hz : 0 <= z) hxy hyz
  have hy : 0 < y := hx.trans_lt hxy
  have hy' : 0 < y ^ p := rpow_pos_of_pos hy _
  trans p * y ^ (p - 1)
  · have q : 0 < y - x := by rwa [sub_pos]
    rw [div_lt_iff₀ q]; rw [← div_lt_div_iff_of_pos_right hy']; rw [_root_.sub_div]; rw [div_self hy'.ne']; rw [← div_rpow hx hy.le]; rw [sub_lt_comm]; rw [← add_sub_cancel_right (x / y) 1]; rw [add_comm]; rw [add_sub_assoc]; rw [← div_mul_eq_mul_div]; rw [mul_div_assoc]; rw [← rpow_sub hy]; rw [sub_sub_cancel_left]; rw [rpow_neg_one]; rw [mul_assoc]; rw [← div_eq_inv_mul]; rw [sub_eq_add_neg]; rw [← mul_neg]; rw [← neg_div]; rw [neg_sub]; rw [_root_.sub_div]; rw [div_self hy.ne']
    apply one_add_mul_self_lt_rpow_one_add _ _ hp
    · rw [le_sub_iff_add_le, neg_add_cancel, div_nonneg_iff]
      exact Or.inl ⟨hx, hy.le⟩
    · rw [sub_ne_zero]
      exact ((div_lt_one hy).mpr hxy).ne
  · have q : 0 < z - y := by rwa [sub_pos]
    rw [lt_div_iff₀ q]; rw [← div_lt_div_iff_of_pos_right hy']; rw [_root_.sub_div]; rw [div_self hy'.ne']; rw [← div_rpow hz hy.le]; rw [lt_sub_iff_add_lt']; rw [← add_sub_cancel_right (z / y) 1]; rw [add_comm _ 1]; rw [add_sub_assoc]; rw [← div_mul_eq_mul_div]; rw [mul_div_assoc]; rw [← rpow_sub hy]; rw [sub_sub_cancel_left]; rw [rpow_neg_one]; rw [mul_assoc]; rw [← div_eq_inv_mul]; rw [_root_.sub_div]; rw [div_self hy.ne']
    apply one_add_mul_self_lt_rpow_one_add _ _ hp
    · rw [le_sub_iff_add_le, neg_add_cancel, div_nonneg_iff]
      exact Or.inl ⟨hz, hy.le⟩
    · rw [sub_ne_zero]
      exact ((one_lt_div hy).mpr hyz).ne'

中文:
定理 strictConvexOn_rpow
  条件: {p : 实数} (hp : 1 < p)
  结论: StrictConvexOn 实数 (左闭右无界区间 0) fun x : 实数 => x ^ p
  证明: by
  apply strictConvexOn_of_slope_strict_mono_adjacent (convex_Ici (0 : Real))
  intro x y z (hx : 0 <= x) (hz : 0 <= z) hxy hyz
  have hy : 0 < y := hx.trans_lt hxy
  have hy' : 0 < y ^ p := rpow_pos_of_pos hy _
  trans p * y ^ (p - 1)
  · have q : 0 < y - x := by rwa [sub_pos]
    rw [div_lt_iff₀ q]; rw [← div_lt_div_iff_of_pos_right hy']; rw [_root_.sub_div]; rw [div_self hy'.ne']; rw [← div_rpow hx hy.le]; rw [sub_lt_comm]; rw [← add_sub_cancel_right (x / y) 1]; rw [add_comm]; rw [add_sub_assoc]; rw [← div_mul_eq_mul_div]; rw [mul_div_assoc]; rw [← rpow_sub hy]; rw [sub_sub_cancel_left]; rw [rpow_neg_one]; rw [mul_assoc]; rw [← div_eq_inv_mul]; rw [sub_eq_add_neg]; rw [← mul_neg]; rw [← neg_div]; rw [neg_sub]; rw [_root_.sub_div]; rw [div_self hy.ne']
    apply one_add_mul_self_lt_rpow_one_add _ _ hp
    · rw [le_sub_iff_add_le, neg_add_cancel, div_nonneg_iff]
      exact Or.inl ⟨hx, hy.le⟩
    · rw [sub_ne_zero]
      exact ((div_lt_one hy).mpr hxy).ne
  · have q : 0 < z - y := by rwa [sub_pos]
    rw [lt_div_iff₀ q]; rw [← div_lt_div_iff_of_pos_right hy']; rw [_root_.sub_div]; rw [div_self hy'.ne']; rw [← div_rpow hz hy.le]; rw [lt_sub_iff_add_lt']; rw [← add_sub_cancel_right (z / y) 1]; rw [add_comm _ 1]; rw [add_sub_assoc]; rw [← div_mul_eq_mul_div]; rw [mul_div_assoc]; rw [← rpow_sub hy]; rw [sub_sub_cancel_left]; rw [rpow_neg_one]; rw [mul_assoc]; rw [← div_eq_inv_mul]; rw [_root_.sub_div]; rw [div_self hy.ne']
    apply one_add_mul_self_lt_rpow_one_add _ _ hp
    · rw [le_sub_iff_add_le, neg_add_cancel, div_nonneg_iff]
      exact Or.inl ⟨hz, hy.le⟩
    · rw [sub_ne_zero]
      exact ((one_lt_div hy).mpr hyz).ne'

Depends on / 依赖: _root_, _root_.sub_div, add_comm, add_sub_assoc, add_sub_cancel_right, convex_Ici, div_lt_div_iff_of_pos_right, div_rpow, div_self, hx.trans_lt, hy.le, rpow_pos_of_pos, strictConvexOn_of_slope_strict_mono_adjacent, sub_div, sub_lt_comm, sub_pos, trans_lt
-/
theorem strictConvexOn_rpow {p : Real} (hp : 1 < p) : StrictConvexOn Real (Ici 0) fun x : Real => x ^ p := by
  apply strictConvexOn_of_slope_strict_mono_adjacent (convex_Ici (0 : Real))
  intro x y z (hx : 0 <= x) (hz : 0 <= z) hxy hyz
  have hy : 0 < y := hx.trans_lt hxy
  have hy' : 0 < y ^ p := rpow_pos_of_pos hy _
  trans p * y ^ (p - 1)
  · have q : 0 < y - x := by rwa [sub_pos]
    rw [div_lt_iff₀ q]; rw [← div_lt_div_iff_of_pos_right hy']; rw [_root_.sub_div]; rw [div_self hy'.ne']; rw [← div_rpow hx hy.le]; rw [sub_lt_comm]; rw [← add_sub_cancel_right (x / y) 1]; rw [add_comm]; rw [add_sub_assoc]; rw [← div_mul_eq_mul_div]; rw [mul_div_assoc]; rw [← rpow_sub hy]; rw [sub_sub_cancel_left]; rw [rpow_neg_one]; rw [mul_assoc]; rw [← div_eq_inv_mul]; rw [sub_eq_add_neg]; rw [← mul_neg]; rw [← neg_div]; rw [neg_sub]; rw [_root_.sub_div]; rw [div_self hy.ne']
    apply one_add_mul_self_lt_rpow_one_add _ _ hp
    · rw [le_sub_iff_add_le, neg_add_cancel, div_nonneg_iff]
      exact Or.inl ⟨hx, hy.le⟩
    · rw [sub_ne_zero]
      exact ((div_lt_one hy).mpr hxy).ne
  · have q : 0 < z - y := by rwa [sub_pos]
    rw [lt_div_iff₀ q]; rw [← div_lt_div_iff_of_pos_right hy']; rw [_root_.sub_div]; rw [div_self hy'.ne']; rw [← div_rpow hz hy.le]; rw [lt_sub_iff_add_lt']; rw [← add_sub_cancel_right (z / y) 1]; rw [add_comm _ 1]; rw [add_sub_assoc]; rw [← div_mul_eq_mul_div]; rw [mul_div_assoc]; rw [← rpow_sub hy]; rw [sub_sub_cancel_left]; rw [rpow_neg_one]; rw [mul_assoc]; rw [← div_eq_inv_mul]; rw [_root_.sub_div]; rw [div_self hy.ne']
    apply one_add_mul_self_lt_rpow_one_add _ _ hp
    · rw [le_sub_iff_add_le, neg_add_cancel, div_nonneg_iff]
      exact Or.inl ⟨hz, hy.le⟩
    · rw [sub_ne_zero]
      exact ((one_lt_div hy).mpr hyz).ne'

/--
theorem `convexOn_rpow` / 定理 `convexOn_rpow`

English:
theorem convexOn_rpow
  given: {p : Real} (hp : 1 <= p)
  statement: ConvexOn Real (Ici 0) fun x : Real => x ^ p
  proof: by
  rcases eq_or_lt_of_le hp with (rfl | hp)
  · simpa using! convexOn_id (convex_Ici _)
  exact (strictConvexOn_rpow hp).convexOn

中文:
定理 convexOn_rpow
  条件: {p : 实数} (hp : 1 <= p)
  结论: ConvexOn 实数 (左闭右无界区间 0) fun x : 实数 => x ^ p
  证明: by
  rcases eq_or_lt_of_le hp with (rfl | hp)
  · simpa using! convexOn_id (convex_Ici _)
  exact (strictConvexOn_rpow hp).convexOn

Depends on / 依赖: convexOn, convexOn_id, convex_Ici, eq_or_lt_of_le, strictConvexOn_rpow
-/
theorem convexOn_rpow {p : Real} (hp : 1 <= p) : ConvexOn Real (Ici 0) fun x : Real => x ^ p := by
  rcases eq_or_lt_of_le hp with (rfl | hp)
  · simpa using! convexOn_id (convex_Ici _)
  exact (strictConvexOn_rpow hp).convexOn

/--
theorem `convexOn_rpow_left` / 定理 `convexOn_rpow_left`

English:
theorem convexOn_rpow_left
  given: {b : Real} (hb : 0 < b)
  statement: ConvexOn Real Set.univ (fun (x : Real) => b ^ x)
  proof: by
  convert! convexOn_exp.comp_linearMap (LinearMap.mul Real Real (Real.log b)) using 1
  ext x
  simp [Real.rpow_def_of_pos hb]

中文:
定理 convexOn_rpow_left
  条件: {b : 实数} (hb : 0 < b)
  结论: ConvexOn 实数 集合.univ (fun (x : 实数) => b ^ x)
  证明: by
  convert! convexOn_exp.comp_linearMap (LinearMap.mul Real Real (Real.log b)) using 1
  ext x
  simp [Real.rpow_def_of_pos hb]

Depends on / 依赖: LinearMap, LinearMap.mul, Real.log, Real.rpow_def_of_pos, comp_linearMap, convert, convexOn_exp, convexOn_exp.comp_linearMap, rpow_def_of_pos
-/
theorem convexOn_rpow_left {b : Real} (hb : 0 < b) : ConvexOn Real Set.univ (fun (x : Real) => b ^ x) := by
  convert! convexOn_exp.comp_linearMap (LinearMap.mul Real Real (Real.log b)) using 1
  ext x
  simp [Real.rpow_def_of_pos hb]

/--
theorem `strictConcaveOn_log_Iio` / 定理 `strictConcaveOn_log_Iio`

English:
theorem strictConcaveOn_log_Iio
  statement: StrictConcaveOn Real (Iio 0) log
  proof: by
  refine ⟨convex_Iio _, ?_⟩
  intro x (hx : x < 0) y (hy : y < 0) hxy a b ha hb hab
  have hx' : 0 < -x := by linarith
  have hy' : 0 < -y := by linarith
  have hxy' : -x != -y := by contrapose hxy; linarith
  calc
    a • log x + b • log y = a • log (-x) + b • log (-y) := by simp_rw [log_neg_eq_log]
    _ < log (a • -x + b • -y) := strictConcaveOn_log_Ioi.2 hx' hy' hxy' ha hb hab
    _ = log (-(a • x + b • y)) := by congr 1; simp only [smul_eq_mul]; ring
    _ = _ := by rw [log_neg_eq_log]

中文:
定理 strictConcaveOn_log_Iio
  结论: StrictConcaveOn 实数 (左无界右开区间 0) log
  证明: by
  refine ⟨convex_Iio _, ?_⟩
  intro x (hx : x < 0) y (hy : y < 0) hxy a b ha hb hab
  have hx' : 0 < -x := by linarith
  have hy' : 0 < -y := by linarith
  have hxy' : -x != -y := by contrapose hxy; linarith
  calc
    a • log x + b • log y = a • log (-x) + b • log (-y) := by simp_rw [log_neg_eq_log]
    _ < log (a • -x + b • -y) := strictConcaveOn_log_Ioi.2 hx' hy' hxy' ha hb hab
    _ = log (-(a • x + b • y)) := by congr 1; simp only [smul_eq_mul]; ring
    _ = _ := by rw [log_neg_eq_log]

Depends on / 依赖: contrapose, convex_Iio, log_neg_eq_log, simp_rw, smul_eq_mul, strictConcaveOn_log_Ioi
-/
theorem strictConcaveOn_log_Iio : StrictConcaveOn Real (Iio 0) log := by
  refine ⟨convex_Iio _, ?_⟩
  intro x (hx : x < 0) y (hy : y < 0) hxy a b ha hb hab
  have hx' : 0 < -x := by linarith
  have hy' : 0 < -y := by linarith
  have hxy' : -x != -y := by contrapose hxy; linarith
  calc
    a • log x + b • log y = a • log (-x) + b • log (-y) := by simp_rw [log_neg_eq_log]
    _ < log (a • -x + b • -y) := strictConcaveOn_log_Ioi.2 hx' hy' hxy' ha hb hab
    _ = log (-(a • x + b • y)) := by congr 1; simp only [smul_eq_mul]; ring
    _ = _ := by rw [log_neg_eq_log]

namespace Real

/--
lemma `exp_mul_le_cosh_add_mul_sinh` / 引理 `exp_mul_le_cosh_add_mul_sinh`

English:
lemma exp_mul_le_cosh_add_mul_sinh
  given: {t : Real} (ht : |t| <= 1) (x : Real)
  proof: by
  rw [abs_le] at ht
  calc
    _ = exp ((1 + t) / 2 * x + (1 - t) / 2 * (-x)) := by ring_nf
    _ <= (1 + t) / 2 * exp x + (1 - t) / 2 * exp (-x) :=
convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) (by linarith) (by linarith) by ring
    _ = _ := by rw [cosh_eq, sinh_eq]; ring

中文:
引理 exp_mul_le_cosh_add_mul_sinh
  条件: {t : 实数} (ht : |t| <= 1) (x : 实数)
  证明: by
  rw [abs_le] at ht
  calc
    _ = exp ((1 + t) / 2 * x + (1 - t) / 2 * (-x)) := by ring_nf
    _ <= (1 + t) / 2 * exp x + (1 - t) / 2 * exp (-x) :=
convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) (by linarith) (by linarith) by ring
    _ = _ := by rw [cosh_eq, sinh_eq]; ring

Depends on / 依赖: Set.mem_univ, abs_le, convexOn_exp, cosh_eq, mem_univ, ring_nf, sinh_eq
-/
lemma exp_mul_le_cosh_add_mul_sinh {t : Real} (ht : |t| <= 1) (x : Real) :
    exp (t * x) <= cosh x + t * sinh x := by
  rw [abs_le] at ht
  calc
    _ = exp ((1 + t) / 2 * x + (1 - t) / 2 * (-x)) := by ring_nf
    _ <= (1 + t) / 2 * exp x + (1 - t) / 2 * exp (-x) :=
convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) (by linarith) (by linarith) by ring
    _ = _ := by rw [cosh_eq, sinh_eq]; ring

end Real
