/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Polynomial bounds for trigonometric functions

## Main statements

This file contains upper and lower bounds for real trigonometric functions in terms
of polynomials. See `Trigonometric.Basic` for more elementary inequalities, establishing
the ranges of these functions, and their monotonicity in suitable intervals.

Here we prove the following:

* `sin_lt`: for `x > 0` we have `sin x < x`.
* `sin_gt_sub_cube`: For `0 < x` we have `x - x ^ 3 / 6 < sin x`.
* `lt_tan`: for `0 < x < π/2` we have `x < tan x`.
* `cos_le_one_div_sqrt_sq_add_one` and `cos_lt_one_div_sqrt_sq_add_one`: for
  `-3 * π / 2 ≤ x ≤ 3 * π / 2`, we have `cos x ≤ 1 / sqrt (x ^ 2 + 1)`, with strict inequality if
  `x ≠ 0`. (This bound is not quite optimal, but not far off)

## Tags

sin, cos, tan, angle
-/

public section

open Set

namespace Real
variable {x : Real}

/--
theorem `sin_lt` / 定理 `sin_lt`

English:
theorem sin_lt
  given: (h : 0 < x)
  statement: sin x < x
  proof: by
  rcases lt_or_ge 1 x with h' | h'
  · exact (sin_le_one x).trans_lt h'
  have hx : |x| = x := abs_of_nonneg h.le
  have := le_of_abs_le (sin_bound <| show |x| <= 1 by rwa [hx])
  rw [sub_le_iff_le_add']; rw [hx] at this
  apply this.trans_lt
  rw [sub_add]; rw [sub_lt_self_iff]; rw [sub_pos]; rw

中文:
定理 sin_lt
  条件: (h : 0 < x)
  结论: sin x < x
  证明: by
  rcases lt_or_ge 1 x with h' | h'
  · exact (sin_le_one x).trans_lt h'
  have hx : |x| = x := abs_of_nonneg h.le
  have := le_of_abs_le (sin_bound <| show |x| <= 1 by rwa [hx])
  rw [sub_le_iff_le_add']; rw [hx] at this
  apply this.trans_lt
  rw [sub_add]; rw [sub_lt_self_iff]; rw [sub_pos]; rw

Depends on / 依赖: abs_of_nonneg, div_eq_mul_inv, h.le, le_of_abs_le, lt_or_ge, mul_lt_mul, pow_le_pow_of_le_one, pow_pos, sin_bound, sin_le_one, sub_add, sub_le_iff_le_add, sub_lt_self_iff, sub_pos, this.trans_lt, trans_lt
-/
theorem sin_lt (h : 0 < x) : sin x < x := by
  rcases lt_or_ge 1 x with h' | h'
  · exact (sin_le_one x).trans_lt h'
  have hx : |x| = x := abs_of_nonneg h.le
  have := le_of_abs_le (sin_bound <| show |x| <= 1 by rwa [hx])
  rw [sub_le_iff_le_add']; rw [hx] at this
  apply this.trans_lt
  rw [sub_add]; rw [sub_lt_self_iff]; rw [sub_pos]; rw [div_eq_mul_inv (x ^ 3)]
  refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos h 3)
  apply pow_le_pow_of_le_one h.le h'
  simp

/--
lemma `sin_le` / 引理 `sin_le`

English:
lemma sin_le
  given: (hx : 0 <= x)
  statement: sin x <= x
  proof: by
  obtain rfl | hx := hx.eq_or_lt
  · simp
  · exact (sin_lt hx).le

中文:
引理 sin_le
  条件: (hx : 0 <= x)
  结论: sin x <= x
  证明: by
  obtain rfl | hx := hx.eq_or_lt
  · simp
  · exact (sin_lt hx).le

Depends on / 依赖: eq_or_lt, hx.eq_or_lt, sin_lt
-/
lemma sin_le (hx : 0 <= x) : sin x <= x := by
  obtain rfl | hx := hx.eq_or_lt
  · simp
  · exact (sin_lt hx).le

/--
lemma `lt_sin` / 引理 `lt_sin`

English:
lemma lt_sin
  given: (hx : x < 0)
  statement: x < sin x
  proof: by simpa using sin_lt neg_pos.2 hx

中文:
引理 lt_sin
  条件: (hx : x < 0)
  结论: x < sin x
  证明: by simpa using sin_lt neg_pos.2 hx

Depends on / 依赖: neg_pos, sin_lt
-/
lemma lt_sin (hx : x < 0) : x < sin x := by simpa using sin_lt neg_pos.2 hx
/--
lemma `le_sin` / 引理 `le_sin`

English:
lemma le_sin
  given: (hx : x <= 0)
  statement: x <= sin x
  proof: by simpa using sin_le neg_nonneg.2 hx

中文:
引理 le_sin
  条件: (hx : x <= 0)
  结论: x <= sin x
  证明: by simpa using sin_le neg_nonneg.2 hx

Depends on / 依赖: neg_nonneg, sin_le
-/
lemma le_sin (hx : x <= 0) : x <= sin x := by simpa using sin_le neg_nonneg.2 hx

/--
theorem `lt_sin_mul` / 定理 `lt_sin_mul`

English:
theorem lt_sin_mul
  given: {x : Real} (hx : 0 < x) (hx' : x < 1)
  statement: x < sin (π / 2 * x)
  proof: by
  simpa [mul_comm x] using
    strictConcaveOn_sin_Icc.2 ⟨le_rfl, pi_pos.le⟩ ⟨pi_div_two_pos.le, half_le_self pi_pos.le⟩
      pi_div_two_pos.ne (sub_pos.2 hx') hx

中文:
定理 lt_sin_mul
  条件: {x : 实数} (hx : 0 < x) (hx' : x < 1)
  结论: x < sin (π / 2 * x)
  证明: by
  simpa [mul_comm x] using
    strictConcaveOn_sin_Icc.2 ⟨le_rfl, pi_pos.le⟩ ⟨pi_div_two_pos.le, half_le_self pi_pos.le⟩
      pi_div_two_pos.ne (sub_pos.2 hx') hx

Depends on / 依赖: half_le_self, le_rfl, mul_comm, pi_div_two_pos, pi_div_two_pos.le, pi_div_two_pos.ne, pi_pos, pi_pos.le, strictConcaveOn_sin_Icc, sub_pos
-/
theorem lt_sin_mul {x : Real} (hx : 0 < x) (hx' : x < 1) : x < sin (π / 2 * x) := by
  simpa [mul_comm x] using
    strictConcaveOn_sin_Icc.2 ⟨le_rfl, pi_pos.le⟩ ⟨pi_div_two_pos.le, half_le_self pi_pos.le⟩
      pi_div_two_pos.ne (sub_pos.2 hx') hx

/--
theorem `le_sin_mul` / 定理 `le_sin_mul`

English:
theorem le_sin_mul
  given: {x : Real} (hx : 0 <= x) (hx' : x <= 1)
  statement: x <= sin (π / 2 * x)
  proof: by
  simpa [mul_comm x] using
    strictConcaveOn_sin_Icc.concaveOn.2 ⟨le_rfl, pi_pos.le⟩
      ⟨pi_div_two_pos.le, half_le_self pi_pos.le⟩ (sub_nonneg.2 hx') hx

中文:
定理 le_sin_mul
  条件: {x : 实数} (hx : 0 <= x) (hx' : x <= 1)
  结论: x <= sin (π / 2 * x)
  证明: by
  simpa [mul_comm x] using
    strictConcaveOn_sin_Icc.concaveOn.2 ⟨le_rfl, pi_pos.le⟩
      ⟨pi_div_two_pos.le, half_le_self pi_pos.le⟩ (sub_nonneg.2 hx') hx

Depends on / 依赖: concaveOn, half_le_self, le_rfl, mul_comm, pi_div_two_pos, pi_div_two_pos.le, pi_pos, pi_pos.le, strictConcaveOn_sin_Icc, strictConcaveOn_sin_Icc.concaveOn, sub_nonneg
-/
theorem le_sin_mul {x : Real} (hx : 0 <= x) (hx' : x <= 1) : x <= sin (π / 2 * x) := by
  simpa [mul_comm x] using
    strictConcaveOn_sin_Icc.concaveOn.2 ⟨le_rfl, pi_pos.le⟩
      ⟨pi_div_two_pos.le, half_le_self pi_pos.le⟩ (sub_nonneg.2 hx') hx

/--
theorem `mul_lt_sin` / 定理 `mul_lt_sin`

English:
theorem mul_lt_sin
  given: {x : Real} (hx : 0 < x) (hx' : x < π / 2)
  statement: 2 / π * x < sin x
  proof: by
  rw [← inv_div]
  simpa [-inv_div, mul_inv_cancel_left₀ pi_div_two_pos.ne'] using @lt_sin_mul ((π / 2)⁻¹ * x)
    (mul_pos (inv_pos.2 pi_div_two_pos) hx) (by rwa [← div_eq_inv_mul, div_lt_one pi_div_two_pos])

中文:
定理 mul_lt_sin
  条件: {x : 实数} (hx : 0 < x) (hx' : x < π / 2)
  结论: 2 / π * x < sin x
  证明: by
  rw [← inv_div]
  simpa [-inv_div, mul_inv_cancel_left₀ pi_div_two_pos.ne'] using @lt_sin_mul ((π / 2)⁻¹ * x)
    (mul_pos (inv_pos.2 pi_div_two_pos) hx) (by rwa [← div_eq_inv_mul, div_lt_one pi_div_two_pos])

Depends on / 依赖: div_eq_inv_mul, div_lt_one, inv_div, inv_pos, lt_sin_mul, mul_pos, pi_div_two_pos, pi_div_two_pos.ne
-/
theorem mul_lt_sin {x : Real} (hx : 0 < x) (hx' : x < π / 2) : 2 / π * x < sin x := by
  rw [← inv_div]
  simpa [-inv_div, mul_inv_cancel_left₀ pi_div_two_pos.ne'] using @lt_sin_mul ((π / 2)⁻¹ * x)
    (mul_pos (inv_pos.2 pi_div_two_pos) hx) (by rwa [← div_eq_inv_mul, div_lt_one pi_div_two_pos])

/--
theorem `mul_le_sin` / 定理 `mul_le_sin`

English:
theorem mul_le_sin
  given: {x : Real} (hx : 0 <= x) (hx' : x <= π / 2)
  statement: 2 / π * x <= sin x
  proof: by
  rw [← inv_div]
  simpa [-inv_div, mul_inv_cancel_left₀ pi_div_two_pos.ne'] using @le_sin_mul ((π / 2)⁻¹ * x)
    (mul_nonneg (inv_nonneg.2 pi_div_two_pos.le) hx)
    (by rwa [← div_eq_inv_mul, div_le_one pi_div_two_pos])

中文:
定理 mul_le_sin
  条件: {x : 实数} (hx : 0 <= x) (hx' : x <= π / 2)
  结论: 2 / π * x <= sin x
  证明: by
  rw [← inv_div]
  simpa [-inv_div, mul_inv_cancel_left₀ pi_div_two_pos.ne'] using @le_sin_mul ((π / 2)⁻¹ * x)
    (mul_nonneg (inv_nonneg.2 pi_div_two_pos.le) hx)
    (by rwa [← div_eq_inv_mul, div_le_one pi_div_two_pos])

Depends on / 依赖: div_eq_inv_mul, div_le_one, inv_div, inv_nonneg, le_sin_mul, mul_nonneg, pi_div_two_pos, pi_div_two_pos.le, pi_div_two_pos.ne
-/
theorem mul_le_sin {x : Real} (hx : 0 <= x) (hx' : x <= π / 2) : 2 / π * x <= sin x := by
  rw [← inv_div]
  simpa [-inv_div, mul_inv_cancel_left₀ pi_div_two_pos.ne'] using @le_sin_mul ((π / 2)⁻¹ * x)
    (mul_nonneg (inv_nonneg.2 pi_div_two_pos.le) hx)
    (by rwa [← div_eq_inv_mul, div_le_one pi_div_two_pos])

/--
lemma `sin_le_mul` / 引理 `sin_le_mul`

English:
lemma sin_le_mul
  given: (hx : -(π / 2) <= x) (hx₀ : x <= 0)
  statement: sin x <= 2 / π * x
  proof: by
  simpa using mul_le_sin (neg_nonneg.2 hx₀) (neg_le.2 hx)

中文:
引理 sin_le_mul
  条件: (hx : -(π / 2) <= x) (hx₀ : x <= 0)
  结论: sin x <= 2 / π * x
  证明: by
  simpa using mul_le_sin (neg_nonneg.2 hx₀) (neg_le.2 hx)

Depends on / 依赖: mul_le_sin, neg_le, neg_nonneg
-/
lemma sin_le_mul (hx : -(π / 2) <= x) (hx₀ : x <= 0) : sin x <= 2 / π * x := by
  simpa using mul_le_sin (neg_nonneg.2 hx₀) (neg_le.2 hx)

/--
lemma `mul_abs_le_abs_sin` / 引理 `mul_abs_le_abs_sin`

English:
lemma mul_abs_le_abs_sin
  given: (hx : |x| <= π / 2)
  statement: 2 / π * |x| <= |sin x|
  proof: by
  wlog hx₀ : 0 <= x
case inr => simpa using this (by rwa [abs_neg]) neg_nonneg.2 le_of_not_ge hx₀
  rw [abs_of_nonneg hx₀] at hx ⊢
  exact (mul_le_sin hx₀ hx).trans (le_abs_self _)

中文:
引理 mul_abs_le_abs_sin
  条件: (hx : |x| <= π / 2)
  结论: 2 / π * |x| <= |sin x|
  证明: by
  wlog hx₀ : 0 <= x
case inr => simpa using this (by rwa [abs_neg]) neg_nonneg.2 le_of_not_ge hx₀
  rw [abs_of_nonneg hx₀] at hx ⊢
  exact (mul_le_sin hx₀ hx).trans (le_abs_self _)

Depends on / 依赖: abs_neg, abs_of_nonneg, le_abs_self, le_of_not_ge, mul_le_sin, neg_nonneg
-/
lemma mul_abs_le_abs_sin (hx : |x| <= π / 2) : 2 / π * |x| <= |sin x| := by
  wlog hx₀ : 0 <= x
case inr => simpa using this (by rwa [abs_neg]) neg_nonneg.2 le_of_not_ge hx₀
  rw [abs_of_nonneg hx₀] at hx ⊢
  exact (mul_le_sin hx₀ hx).trans (le_abs_self _)

/--
lemma `sin_sq_lt_sq` / 引理 `sin_sq_lt_sq`

English:
lemma sin_sq_lt_sq
  given: (hx : x != 0)
  statement: sin x ^ 2 < x ^ 2
  proof: by
  wlog! hx₀ : 0 < x
  case inr =>
simpa using this (neg_ne_zero.2 hx) neg_pos_of_neg hx.lt_of_le hx₀
  rcases le_or_gt x 1 with hxπ | hxπ
  case inl =>
    exact pow_lt_pow_left₀ (sin_lt hx₀)
      (sin_nonneg_of_nonneg_of_le_pi hx₀.le (by linarith [two_le_pi])) (by simp)
  case inr =>
    exact 

中文:
引理 sin_sq_lt_sq
  条件: (hx : x != 0)
  结论: sin x ^ 2 < x ^ 2
  证明: by
  wlog! hx₀ : 0 < x
  case inr =>
simpa using this (neg_ne_zero.2 hx) neg_pos_of_neg hx.lt_of_le hx₀
  rcases le_or_gt x 1 with hxπ | hxπ
  case inl =>
    exact pow_lt_pow_left₀ (sin_lt hx₀)
      (sin_nonneg_of_nonneg_of_le_pi hx₀.le (by linarith [two_le_pi])) (by simp)
  case inr =>
    exact 

Depends on / 依赖: hx.lt_of_le, le_or_gt, lt_of_le, neg_ne_zero, neg_pos_of_neg, sin_lt, sin_nonneg_of_nonneg_of_le_pi, sin_sq_le_one, trans_lt, two_le_pi
-/
lemma sin_sq_lt_sq (hx : x != 0) : sin x ^ 2 < x ^ 2 := by
  wlog! hx₀ : 0 < x
  case inr =>
simpa using this (neg_ne_zero.2 hx) neg_pos_of_neg hx.lt_of_le hx₀
  rcases le_or_gt x 1 with hxπ | hxπ
  case inl =>
    exact pow_lt_pow_left₀ (sin_lt hx₀)
      (sin_nonneg_of_nonneg_of_le_pi hx₀.le (by linarith [two_le_pi])) (by simp)
  case inr =>
    exact (sin_sq_le_one _).trans_lt (by rwa [one_lt_sq_iff₀ hx₀.le])

/--
lemma `sin_sq_le_sq` / 引理 `sin_sq_le_sq`

English:
lemma sin_sq_le_sq
  statement: sin x ^ 2 <= x ^ 2
  proof: by
  rcases eq_or_ne x 0 with rfl | hx
  case inl => simp
  case inr => exact (sin_sq_lt_sq hx).le

中文:
引理 sin_sq_le_sq
  结论: sin x ^ 2 <= x ^ 2
  证明: by
  rcases eq_or_ne x 0 with rfl | hx
  case inl => simp
  case inr => exact (sin_sq_lt_sq hx).le

Depends on / 依赖: eq_or_ne, sin_sq_lt_sq
-/
lemma sin_sq_le_sq : sin x ^ 2 <= x ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  case inl => simp
  case inr => exact (sin_sq_lt_sq hx).le

/--
lemma `abs_sin_lt_abs` / 引理 `abs_sin_lt_abs`

English:
lemma abs_sin_lt_abs
  given: (hx : x != 0)
  statement: |sin x| < |x|
  proof: sq_lt_sq.1 (sin_sq_lt_sq hx)

中文:
引理 abs_sin_lt_abs
  条件: (hx : x != 0)
  结论: |sin x| < |x|
  证明: sq_lt_sq.1 (sin_sq_lt_sq hx)

Depends on / 依赖: sin_sq_lt_sq, sq_lt_sq
-/
lemma abs_sin_lt_abs (hx : x != 0) : |sin x| < |x| := sq_lt_sq.1 (sin_sq_lt_sq hx)
/--
lemma `abs_sin_le_abs` / 引理 `abs_sin_le_abs`

English:
lemma abs_sin_le_abs
  statement: |sin x| <= |x|
  proof: sq_le_sq.1 sin_sq_le_sq

中文:
引理 abs_sin_le_abs
  结论: |sin x| <= |x|
  证明: sq_le_sq.1 sin_sq_le_sq

Depends on / 依赖: Comma.preLeft, Faithful, preLeft, sin_sq_le_sq, sq_le_sq
-/
lemma abs_sin_le_abs : |sin x| <= |x| := sq_le_sq.1 sin_sq_le_sq

/--
lemma `one_sub_sq_div_two_lt_cos` / 引理 `one_sub_sq_div_two_lt_cos`

English:
lemma one_sub_sq_div_two_lt_cos
  given: (hx : x != 0)
  statement: 1 - x ^ 2 / 2 < cos x
  proof: by
  have := (sin_sq_lt_sq (by positivity)).trans_eq' (sin_sq_eq_half_sub (x / 2))
  ring_nf at this
  linarith

中文:
引理 one_sub_sq_div_two_lt_cos
  条件: (hx : x != 0)
  结论: 1 - x ^ 2 / 2 < cos x
  证明: by
  have := (sin_sq_lt_sq (by positivity)).trans_eq' (sin_sq_eq_half_sub (x / 2))
  ring_nf at this
  linarith

Depends on / 依赖: Comma.preLeft, preLeft, ring_nf, sin_sq_eq_half_sub, sin_sq_lt_sq, trans_eq
-/
lemma one_sub_sq_div_two_lt_cos (hx : x != 0) : 1 - x ^ 2 / 2 < cos x := by
  have := (sin_sq_lt_sq (by positivity)).trans_eq' (sin_sq_eq_half_sub (x / 2))
  ring_nf at this
  linarith

/--
lemma `one_sub_sq_div_two_le_cos` / 引理 `one_sub_sq_div_two_le_cos`

English:
lemma one_sub_sq_div_two_le_cos
  statement: 1 - x ^ 2 / 2 <= cos x
  proof: by
  rcases eq_or_ne x 0 with rfl | hx
  case inl => simp
  case inr => exact (one_sub_sq_div_two_lt_cos hx).le

中文:
引理 one_sub_sq_div_two_le_cos
  结论: 1 - x ^ 2 / 2 <= cos x
  证明: by
  rcases eq_or_ne x 0 with rfl | hx
  case inl => simp
  case inr => exact (one_sub_sq_div_two_lt_cos hx).le

Depends on / 依赖: Comma.preLeft, EssSurj, eq_or_ne, one_sub_sq_div_two_lt_cos, preLeft
-/
lemma one_sub_sq_div_two_le_cos : 1 - x ^ 2 / 2 <= cos x := by
  rcases eq_or_ne x 0 with rfl | hx
  case inl => simp
  case inr => exact (one_sub_sq_div_two_lt_cos hx).le

/--
lemma `one_sub_mul_le_cos` / 引理 `one_sub_mul_le_cos`

English:
lemma one_sub_mul_le_cos
  given: (hx₀ : 0 <= x) (hx : x <= π / 2)
  statement: 1 - 2 / π * x <= cos x
  proof: by
  simpa [sin_pi_div_two_sub, mul_sub, div_mul_div_comm, mul_comm π, pi_pos.ne']
    using mul_le_sin (x := π / 2 - x) (by simpa) (by simpa)

中文:
引理 one_sub_mul_le_cos
  条件: (hx₀ : 0 <= x) (hx : x <= π / 2)
  结论: 1 - 2 / π * x <= cos x
  证明: by
  simpa [sin_pi_div_two_sub, mul_sub, div_mul_div_comm, mul_comm π, pi_pos.ne']
    using mul_le_sin (x := π / 2 - x) (by simpa) (by simpa)

Depends on / 依赖: div_mul_div_comm, mul_comm, mul_le_sin, mul_sub, pi_pos, pi_pos.ne, sin_pi_div_two_sub
-/
lemma one_sub_mul_le_cos (hx₀ : 0 <= x) (hx : x <= π / 2) : 1 - 2 / π * x <= cos x := by
  simpa [sin_pi_div_two_sub, mul_sub, div_mul_div_comm, mul_comm π, pi_pos.ne']
    using mul_le_sin (x := π / 2 - x) (by simpa) (by simpa)

/--
lemma `one_add_mul_le_cos` / 引理 `one_add_mul_le_cos`

English:
lemma one_add_mul_le_cos
  given: (hx₀ : -(π / 2) <= x) (hx : x <= 0)
  statement: 1 + 2 / π * x <= cos x
  proof: by
  simpa using one_sub_mul_le_cos (x := -x) (by linarith) (by linarith)

中文:
引理 one_add_mul_le_cos
  条件: (hx₀ : -(π / 2) <= x) (hx : x <= 0)
  结论: 1 + 2 / π * x <= cos x
  证明: by
  simpa using one_sub_mul_le_cos (x := -x) (by linarith) (by linarith)

Depends on / 依赖: one_sub_mul_le_cos
-/
lemma one_add_mul_le_cos (hx₀ : -(π / 2) <= x) (hx : x <= 0) : 1 + 2 / π * x <= cos x := by
  simpa using one_sub_mul_le_cos (x := -x) (by linarith) (by linarith)

/--
lemma `cos_le_one_sub_mul_cos_sq` / 引理 `cos_le_one_sub_mul_cos_sq`

English:
lemma cos_le_one_sub_mul_cos_sq
  given: (hx : |x| <= π)
  statement: cos x <= 1 - 2 / π ^ 2 * x ^ 2
  proof: by
  wlog hx₀ : 0 <= x
case inr => simpa using this (by rwa [abs_neg]) neg_nonneg.2 le_of_not_ge hx₀
  rw [abs_of_nonneg hx₀] at hx
  have : x / π <= sin (x / 2) := by simpa using mul_le_sin (x := x / 2) (by positivity) (by linarith)
  have := (pow_le_pow_left₀ (by positivity) this 2).trans_eq (sin_

中文:
引理 cos_le_one_sub_mul_cos_sq
  条件: (hx : |x| <= π)
  结论: cos x <= 1 - 2 / π ^ 2 * x ^ 2
  证明: by
  wlog hx₀ : 0 <= x
case inr => simpa using this (by rwa [abs_neg]) neg_nonneg.2 le_of_not_ge hx₀
  rw [abs_of_nonneg hx₀] at hx
  have : x / π <= sin (x / 2) := by simpa using mul_le_sin (x := x / 2) (by positivity) (by linarith)
  have := (pow_le_pow_left₀ (by positivity) this 2).trans_eq (sin_

Depends on / 依赖: abs_neg, abs_of_nonneg, ext_iff, le_of_not_ge, mul_le_sin, neg_nonneg, ring_nf, sin_sq_eq_half_sub, trans_eq
-/
lemma cos_le_one_sub_mul_cos_sq (hx : |x| <= π) : cos x <= 1 - 2 / π ^ 2 * x ^ 2 := by
  wlog hx₀ : 0 <= x
case inr => simpa using this (by rwa [abs_neg]) neg_nonneg.2 le_of_not_ge hx₀
  rw [abs_of_nonneg hx₀] at hx
  have : x / π <= sin (x / 2) := by simpa using mul_le_sin (x := x / 2) (by positivity) (by linarith)
  have := (pow_le_pow_left₀ (by positivity) this 2).trans_eq (sin_sq_eq_half_sub _)
  ring_nf at this ⊢
  linarith

/--
theorem `sin_gt_sub_cube` / 定理 `sin_gt_sub_cube`

English:
theorem sin_gt_sub_cube
  given: {x : Real} (hx : 0 < x)
  statement: x - x ^ 3 / 6 < Real.sin x
  proof: by
  let f (t : Real) : Real := Real.sin t - (t - t ^ 3 / 6)
  have hderiv (t : Real) : deriv f t = cos t - 1 + t ^ 2 / 2 := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : StrictMonoOn f (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop)
    grind [one_su

中文:
定理 sin_gt_sub_cube
  条件: {x : 实数} (hx : 0 < x)
  结论: x - x ^ 3 / 6 < 实数.sin x
  证明: by
  let f (t : Real) : Real := Real.sin t - (t - t ^ 3 / 6)
  have hderiv (t : Real) : deriv f t = cos t - 1 + t ^ 2 / 2 := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : StrictMonoOn f (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop)
    grind [one_su

Depends on / 依赖: G.map_injective, Real.sin, Real.sin_zero, Set.Ici, StrictMonoOn, convex_Ici, f.left, fun_prop, hderiv, hx.le, interior_Ici, map_injective, one_sub_sq_div_two_lt_cos, sin_zero, strictMonoOn_of_deriv_pos
-/
theorem sin_gt_sub_cube {x : Real} (hx : 0 < x) : x - x ^ 3 / 6 < Real.sin x := by
  let f (t : Real) : Real := Real.sin t - (t - t ^ 3 / 6)
  have hderiv (t : Real) : deriv f t = cos t - 1 + t ^ 2 / 2 := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : StrictMonoOn f (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop)
    grind [one_sub_sq_div_two_lt_cos, interior_Ici]
  have h0 : f 0 < f x := hmono (by simp) hx.le hx
  grind [Real.sin_zero]

/--
theorem `sin_ge_sub_cube` / 定理 `sin_ge_sub_cube`

English:
theorem sin_ge_sub_cube
  given: {x : Real} (hx : 0 <= x)
  statement: x - x ^ 3 / 6 <= Real.sin x
  proof: by
  obtain rfl | hx := hx.eq_or_lt
  · simp
  exact (sin_gt_sub_cube hx).le

中文:
定理 sin_ge_sub_cube
  条件: {x : 实数} (hx : 0 <= x)
  结论: x - x ^ 3 / 6 <= 实数.sin x
  证明: by
  obtain rfl | hx := hx.eq_or_lt
  · simp
  exact (sin_gt_sub_cube hx).le

Depends on / 依赖: G.preimage, Iso.refl, eq_or_lt, h.hom, hx.eq_or_lt, preimage, sin_gt_sub_cube
-/
theorem sin_ge_sub_cube {x : Real} (hx : 0 <= x) : x - x ^ 3 / 6 <= Real.sin x := by
  obtain rfl | hx := hx.eq_or_lt
  · simp
  exact (sin_gt_sub_cube hx).le

/--
theorem `abs_sub_sin_le` / 定理 `abs_sub_sin_le`

English:
theorem abs_sub_sin_le
  given: (x : Real)
  statement: |x - Real.sin x| <= |x| ^ 3 / 6
  proof: by
  wlog hx : 0 <= x
  · grind [sin_neg]
  · grind [Real.sin_le, abs_of_nonneg, sin_ge_sub_cube]

中文:
定理 abs_sub_sin_le
  条件: (x : 实数)
  结论: |x - 实数.sin x| <= |x| ^ 3 / 6
  证明: by
  wlog hx : 0 <= x
  · grind [sin_neg]
  · grind [Real.sin_le, abs_of_nonneg, sin_ge_sub_cube]

Depends on / 依赖: Real.sin_le, abs_of_nonneg, sin_ge_sub_cube, sin_le, sin_neg
-/
theorem abs_sub_sin_le (x : Real) : |x - Real.sin x| <= |x| ^ 3 / 6 := by
  wlog hx : 0 <= x
  · grind [sin_neg]
  · grind [Real.sin_le, abs_of_nonneg, sin_ge_sub_cube]

/--
theorem `deriv_tan_sub_id` / 定理 `deriv_tan_sub_id`

English:
theorem deriv_tan_sub_id
  given: (x : Real) (h : cos x != 0)
  proof: HasDerivAt.deriv by simpa using! (hasDerivAt_tan h).add (hasDerivAt_id x).neg

中文:
定理 deriv_tan_sub_id
  条件: (x : 实数) (h : cos x != 0)
  证明: HasDerivAt.deriv by simpa using! (hasDerivAt_tan h).add (hasDerivAt_id x).neg

Depends on / 依赖: HasDerivAt, HasDerivAt.deriv, hasDerivAt_id, hasDerivAt_tan
-/
theorem deriv_tan_sub_id (x : Real) (h : cos x != 0) :
    deriv (fun y : Real => tan y - y) x = 1 / cos x ^ 2 - 1 :=
HasDerivAt.deriv by simpa using! (hasDerivAt_tan h).add (hasDerivAt_id x).neg

/--
theorem `lt_tan` / 定理 `lt_tan`

English:
theorem lt_tan
  given: {x : Real} (h1 : 0 < x) (h2 : x < π / 2)
  statement: x < tan x
  proof: by
  let U := Ico 0 (π / 2)
  have intU : interior U = Ioo 0 (π / 2) := interior_Ico
  have half_pi_pos : 0 < π / 2 := div_pos pi_pos two_pos
  have cos_pos {y : Real} (hy : y in U) : 0 < cos y := by
    exact cos_pos_of_mem_Ioo (Ico_subset_Ioo_left (neg_lt_zero.mpr half_pi_pos) hy)
  have sin_pos {

中文:
定理 lt_tan
  条件: {x : 实数} (h1 : 0 < x) (h2 : x < π / 2)
  结论: x < tan x
  证明: by
  let U := Ico 0 (π / 2)
  have intU : interior U = Ioo 0 (π / 2) := interior_Ico
  have half_pi_pos : 0 < π / 2 := div_pos pi_pos two_pos
  have cos_pos {y : Real} (hy : y in U) : 0 < cos y := by
    exact cos_pos_of_mem_Ioo (Ico_subset_Ioo_left (neg_lt_zero.mpr half_pi_pos) hy)
  have sin_pos {

Depends on / 依赖: ContinuousOn, Ico_subset_Ioo_left, Ioo_subset_Ioo_right, cos_pos, cos_pos_of_mem_Ioo, div_le_self, div_pos, half_pi_pos, interior, interior_Ico, neg_lt_zero, neg_lt_zero.mpr, one_le_two, pi_pos, pi_pos.le, sin_pos, sin_pos_of_mem_Ioo, tan_cts_U, two_pos
-/
theorem lt_tan {x : Real} (h1 : 0 < x) (h2 : x < π / 2) : x < tan x := by
  let U := Ico 0 (π / 2)
  have intU : interior U = Ioo 0 (π / 2) := interior_Ico
  have half_pi_pos : 0 < π / 2 := div_pos pi_pos two_pos
  have cos_pos {y : Real} (hy : y in U) : 0 < cos y := by
    exact cos_pos_of_mem_Ioo (Ico_subset_Ioo_left (neg_lt_zero.mpr half_pi_pos) hy)
  have sin_pos {y : Real} (hy : y in interior U) : 0 < sin y := by
    rw [intU] at hy
    exact sin_pos_of_mem_Ioo (Ioo_subset_Ioo_right (div_le_self pi_pos.le one_le_two) hy)
  have tan_cts_U : ContinuousOn tan U := by
    apply ContinuousOn.mono continuousOn_tan
    intro z hz
    simp only [mem_ofPred_eq]
    exact (cos_pos hz).ne'
  have tan_minus_id_cts : ContinuousOn (fun y : Real => tan y - y) U := tan_cts_U.sub continuousOn_id
  have deriv_pos (y : Real) (hy : y in interior U) : 0 < deriv (fun y' : Real => tan y' - y') y := by
    have := cos_pos (interior_subset hy)
    simp only [deriv_tan_sub_id y this.ne', one_div, gt_iff_lt, sub_pos]
    norm_cast
    have bd2 : cos y ^ 2 < 1 := by
      apply lt_of_le_of_ne y.cos_sq_le_one
      rw [cos_sq']
      simpa only [Ne, sub_eq_self, sq_eq_zero_iff] using (sin_pos hy).ne'
    rwa [lt_inv_comm₀, inv_one]
    · exact zero_lt_one
    simpa only [sq, mul_self_pos] using this.ne'
  have mono := strictMonoOn_of_deriv_pos (convex_Ico 0 (π / 2)) tan_minus_id_cts deriv_pos
  have zero_in_U : (0 : Real) in U := by rwa [left_mem_Ico]
  have x_in_U : x in U := ⟨h1.le, h2⟩
  simpa only [tan_zero, sub_zero, sub_pos] using mono zero_in_U x_in_U h1

/--
theorem `le_tan` / 定理 `le_tan`

English:
theorem le_tan
  given: {x : Real} (h1 : 0 <= x) (h2 : x < π / 2)
  statement: x <= tan x
  proof: by
  rcases eq_or_lt_of_le h1 with (rfl | h1')
  · rw [tan_zero]
  · exact le_of_lt (lt_tan h1' h2)

中文:
定理 le_tan
  条件: {x : 实数} (h1 : 0 <= x) (h2 : x < π / 2)
  结论: x <= tan x
  证明: by
  rcases eq_or_lt_of_le h1 with (rfl | h1')
  · rw [tan_zero]
  · exact le_of_lt (lt_tan h1' h2)

Depends on / 依赖: eq_or_lt_of_le, le_of_lt, lt_tan, tan_zero
-/
theorem le_tan {x : Real} (h1 : 0 <= x) (h2 : x < π / 2) : x <= tan x := by
  rcases eq_or_lt_of_le h1 with (rfl | h1')
  · rw [tan_zero]
  · exact le_of_lt (lt_tan h1' h2)

/--
theorem `cos_lt_one_div_sqrt_sq_add_one` / 定理 `cos_lt_one_div_sqrt_sq_add_one`

English:
theorem cos_lt_one_div_sqrt_sq_add_one
  statement: {x : Real} (hx1 : -(3 * π / 2) <= x) (hx2 : x <= 3 * π / 2)
  proof: by
  suffices forall {y : Real}, 0 < y -> y <= 3 * π / 2 -> cos y < 1 / √(y ^ 2 + 1) by
    rcases lt_or_lt_iff_ne.mpr hx3.symm with ⟨h⟩
    · exact this h hx2
    · convert! this (by linarith : 0 < -x) (by linarith) using 1
      · rw [cos_neg]
      · rw [neg_sq]
  intro y hy1 hy2
  have hy3 : ↑0 

中文:
定理 cos_lt_one_div_sqrt_sq_add_one
  结论: {x : 实数} (hx1 : -(3 * π / 2) <= x) (hx2 : x <= 3 * π / 2)
  证明: by
  suffices forall {y : Real}, 0 < y -> y <= 3 * π / 2 -> cos y < 1 / √(y ^ 2 + 1) by
    rcases lt_or_lt_iff_ne.mpr hx3.symm with ⟨h⟩
    · exact this h hx2
    · convert! this (by linarith : 0 < -x) (by linarith) using 1
      · rw [cos_neg]
      · rw [neg_sq]
  intro y hy1 hy2
  have hy3 : ↑0 

Depends on / 依赖: abs_of_nonneg, convert, cos_neg, cos_nonneg_of_mem_Icc, cos_pos_of_mem_Ioo, hx3.symm, lt_or_ge, lt_or_lt_iff_ne, lt_or_lt_iff_ne.mpr, neg_sq, sq_nonneg
-/
theorem cos_lt_one_div_sqrt_sq_add_one {x : Real} (hx1 : -(3 * π / 2) <= x) (hx2 : x <= 3 * π / 2)
    (hx3 : x != 0) : cos x < (1 / √(x ^ 2 + 1) : Real) := by
  suffices forall {y : Real}, 0 < y -> y <= 3 * π / 2 -> cos y < 1 / √(y ^ 2 + 1) by
    rcases lt_or_lt_iff_ne.mpr hx3.symm with ⟨h⟩
    · exact this h hx2
    · convert! this (by linarith : 0 < -x) (by linarith) using 1
      · rw [cos_neg]
      · rw [neg_sq]
  intro y hy1 hy2
  have hy3 : ↑0 < y ^ 2 + 1 := by linarith [sq_nonneg y]
  rcases lt_or_ge y (π / 2) with (hy2' | hy1')
  · -- Main case : `0 < y < π / 2`
    have hy4 : 0 < cos y := cos_pos_of_mem_Ioo ⟨by linarith, hy2'⟩
    rw [← abs_of_nonneg (cos_nonneg_of_mem_Icc ⟨by linarith]; rw [hy2'.le⟩)]; rw [←
      abs_of_nonneg (one_div_nonneg.mpr (sqrt_nonneg _))]; rw [← sq_lt_sq]; rw [div_pow]; rw [one_pow]; rw [sq_sqrt hy3.le]; rw [lt_one_div (pow_pos hy4 _) hy3]; rw [← inv_one_add_tan_sq hy4.ne']; rw [one_div]; rw [inv_inv]; rw [add_comm]; rw [add_lt_add_iff_left]; rw [sq_lt_sq]; rw [abs_of_pos hy1]; rw [abs_of_nonneg (tan_nonneg_of_nonneg_of_le_pi_div_two hy1.le hy2'.le)]
    exact Real.lt_tan hy1 hy2'
  · -- Easy case : `π / 2 ≤ y ≤ 3 * π / 2`
    refine lt_of_le_of_lt ?_ (one_div_pos.mpr <| sqrt_pos_of_pos hy3)
    exact cos_nonpos_of_pi_div_two_le_of_le hy1' (by linarith [pi_pos])

/--
theorem `cos_le_one_div_sqrt_sq_add_one` / 定理 `cos_le_one_div_sqrt_sq_add_one`

English:
theorem cos_le_one_div_sqrt_sq_add_one
  given: {x : Real} (hx1 : -(3 * π / 2) <= x) (hx2 : x <= 3 * π / 2)
  proof: by
  rcases eq_or_ne x 0 with (rfl | hx3)
  · simp
  · exact (cos_lt_one_div_sqrt_sq_add_one hx1 hx2 hx3).le

中文:
定理 cos_le_one_div_sqrt_sq_add_one
  条件: {x : 实数} (hx1 : -(3 * π / 2) <= x) (hx2 : x <= 3 * π / 2)
  证明: by
  rcases eq_or_ne x 0 with (rfl | hx3)
  · simp
  · exact (cos_lt_one_div_sqrt_sq_add_one hx1 hx2 hx3).le

Depends on / 依赖: cos_lt_one_div_sqrt_sq_add_one, eq_or_ne
-/
theorem cos_le_one_div_sqrt_sq_add_one {x : Real} (hx1 : -(3 * π / 2) <= x) (hx2 : x <= 3 * π / 2) :
    cos x <= (1 : Real) / √(x ^ 2 + 1) := by
  rcases eq_or_ne x 0 with (rfl | hx3)
  · simp
  · exact (cos_lt_one_div_sqrt_sq_add_one hx1 hx2 hx3).le

/--
theorem `lipschitzWith_sin` / 定理 `lipschitzWith_sin`

English:
theorem lipschitzWith_sin
  statement: LipschitzWith 1 sin
  proof: lipschitzWith_of_nnnorm_deriv_le differentiable_sin by simpa using! abs_cos_le_one

中文:
定理 lipschitzWith_sin
  结论: LipschitzWith 1 sin
  证明: lipschitzWith_of_nnnorm_deriv_le differentiable_sin by simpa using! abs_cos_le_one

Depends on / 依赖: abs_cos_le_one, differentiable_sin, lipschitzWith_of_nnnorm_deriv_le
-/
theorem lipschitzWith_sin : LipschitzWith 1 sin :=
lipschitzWith_of_nnnorm_deriv_le differentiable_sin by simpa using! abs_cos_le_one

/--
theorem `lipschitzWith_cos` / 定理 `lipschitzWith_cos`

English:
theorem lipschitzWith_cos
  statement: LipschitzWith 1 cos
  proof: lipschitzWith_of_nnnorm_deriv_le differentiable_cos by simpa using! abs_sin_le_one

中文:
定理 lipschitzWith_cos
  结论: LipschitzWith 1 cos
  证明: lipschitzWith_of_nnnorm_deriv_le differentiable_cos by simpa using! abs_sin_le_one

Depends on / 依赖: abs_sin_le_one, differentiable_cos, lipschitzWith_of_nnnorm_deriv_le
-/
theorem lipschitzWith_cos : LipschitzWith 1 cos :=
lipschitzWith_of_nnnorm_deriv_le differentiable_cos by simpa using! abs_sin_le_one

/--
theorem `abs_sin_sub_sin_le` / 定理 `abs_sin_sub_sin_le`

English:
theorem abs_sin_sub_sin_le
  given: (x y : Real)
  statement: |sin x - sin y| <= |x - y|
  proof: by
  simpa [edist_dist] using! lipschitzWith_sin x y

中文:
定理 abs_sin_sub_sin_le
  条件: (x y : 实数)
  结论: |sin x - sin y| <= |x - y|
  证明: by
  simpa [edist_dist] using! lipschitzWith_sin x y

Depends on / 依赖: edist_dist, lipschitzWith_sin
-/
theorem abs_sin_sub_sin_le (x y : Real) : |sin x - sin y| <= |x - y| := by
  simpa [edist_dist] using! lipschitzWith_sin x y

/--
theorem `abs_cos_sub_cos_le` / 定理 `abs_cos_sub_cos_le`

English:
theorem abs_cos_sub_cos_le
  given: (x y : Real)
  statement: |cos x - cos y| <= |x - y|
  proof: by
  simpa [edist_dist] using! lipschitzWith_cos x y

中文:
定理 abs_cos_sub_cos_le
  条件: (x y : 实数)
  结论: |cos x - cos y| <= |x - y|
  证明: by
  simpa [edist_dist] using! lipschitzWith_cos x y

Depends on / 依赖: edist_dist, lipschitzWith_cos
-/
theorem abs_cos_sub_cos_le (x y : Real) : |cos x - cos y| <= |x - y| := by
  simpa [edist_dist] using! lipschitzWith_cos x y

/--
theorem `norm_exp_I_mul_ofReal_sub_one_le` / 定理 `norm_exp_I_mul_ofReal_sub_one_le`

English:
theorem norm_exp_I_mul_ofReal_sub_one_le
  given: {x : Real}
  statement: ‖.exp (.I * x) - (1 : Complex)‖ <= ‖x‖
  proof: by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  calc
    _ = 2 * |Real.sin (x / 2)| := by simp
    _ <= 2 * |x / 2| := (mul_le_mul_iff_of_pos_left zero_lt_two).mpr Real.abs_sin_le_abs
    _ = _ := by rw [abs_div, Nat.abs_ofNat, Real.norm_eq_abs]; ring

中文:
定理 norm_exp_I_mul_of实数_sub_one_le
  条件: {x : 实数}
  结论: ‖.exp (.I * x) - (1 : 复形)‖ <= ‖x‖
  证明: by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  calc
    _ = 2 * |Real.sin (x / 2)| := by simp
    _ <= 2 * |x / 2| := (mul_le_mul_iff_of_pos_left zero_lt_two).mpr Real.abs_sin_le_abs
    _ = _ := by rw [abs_div, Nat.abs_ofNat, Real.norm_eq_abs]; ring

Depends on / 依赖: Complex.norm_exp_I_mul_ofReal_sub_one, Nat.abs_ofNat, Real.abs_sin_le_abs, Real.norm_eq_abs, Real.sin, abs_div, abs_ofNat, abs_sin_le_abs, mul_le_mul_iff_of_pos_left, norm_eq_abs, norm_exp_I_mul_ofReal_sub_one, zero_lt_two
-/
theorem norm_exp_I_mul_ofReal_sub_one_le {x : Real} : ‖.exp (.I * x) - (1 : Complex)‖ <= ‖x‖ := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  calc
    _ = 2 * |Real.sin (x / 2)| := by simp
    _ <= 2 * |x / 2| := (mul_le_mul_iff_of_pos_left zero_lt_two).mpr Real.abs_sin_le_abs
    _ = _ := by rw [abs_div, Nat.abs_ofNat, Real.norm_eq_abs]; ring

/--
theorem `enorm_exp_I_mul_ofReal_sub_one_le` / 定理 `enorm_exp_I_mul_ofReal_sub_one_le`

English:
theorem enorm_exp_I_mul_ofReal_sub_one_le
  given: {x : Real}
  statement: ‖.exp (.I * x) - (1 : Complex)‖ₑ <= ‖x‖ₑ
  proof: by
  iterate 2 rw [← enorm_norm, Real.enorm_of_nonneg (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal norm_exp_I_mul_ofReal_sub_one_le

中文:
定理 enorm_exp_I_mul_of实数_sub_one_le
  条件: {x : 实数}
  结论: ‖.exp (.I * x) - (1 : 复形)‖ₑ <= ‖x‖ₑ
  证明: by
  iterate 2 rw [← enorm_norm, Real.enorm_of_nonneg (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal norm_exp_I_mul_ofReal_sub_one_le

Depends on / 依赖: ENNReal, ENNReal.ofReal_le_ofReal, Real.enorm_of_nonneg, enorm_norm, enorm_of_nonneg, iterate, norm_exp_I_mul_ofReal_sub_one_le, norm_nonneg, ofReal_le_ofReal
-/
theorem enorm_exp_I_mul_ofReal_sub_one_le {x : Real} : ‖.exp (.I * x) - (1 : Complex)‖ₑ <= ‖x‖ₑ := by
  iterate 2 rw [← enorm_norm, Real.enorm_of_nonneg (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal norm_exp_I_mul_ofReal_sub_one_le

/--
theorem `nnnorm_exp_I_mul_ofReal_sub_one_le` / 定理 `nnnorm_exp_I_mul_ofReal_sub_one_le`

English:
theorem nnnorm_exp_I_mul_ofReal_sub_one_le
  given: {x : Real}
  statement: ‖.exp (.I * x) - (1 : Complex)‖₊ <= ‖x‖₊
  proof: by
  rw [← ENNReal.coe_le_coe]; exact enorm_exp_I_mul_ofReal_sub_one_le

中文:
定理 nnnorm_exp_I_mul_of实数_sub_one_le
  条件: {x : 实数}
  结论: ‖.exp (.I * x) - (1 : 复形)‖₊ <= ‖x‖₊
  证明: by
  rw [← ENNReal.coe_le_coe]; exact enorm_exp_I_mul_ofReal_sub_one_le

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, coe_le_coe, enorm_exp_I_mul_ofReal_sub_one_le
-/
theorem nnnorm_exp_I_mul_ofReal_sub_one_le {x : Real} : ‖.exp (.I * x) - (1 : Complex)‖₊ <= ‖x‖₊ := by
  rw [← ENNReal.coe_le_coe]; exact enorm_exp_I_mul_ofReal_sub_one_le

end Real
