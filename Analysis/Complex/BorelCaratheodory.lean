/-
Copyright (c) 2026 Maksym Radziwill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maksym Radziwill
-/

module

public import Mathlib.Analysis.Complex.Schwarz

/-!
# Borel-Carathéodory theorem

This file proves the Borel-Carathéodory theorem: for any function `f` analytic on the
open ball `|z| < R` such that `Re(f z) < M` for all `|z| < R`, we have
`‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖)`

## Main results

* `Complex.borelCaratheodory_zero`: The theorem under the assumption `f 0 = 0`
* `Complex.borelCaratheodory`: The general version of the theorem

## Implementation Notes

The proof applies the Schwarz lemma to the transformed function `w z := f z / (2 * M - f z)`,
which maps the ball `|z| < R` into the unit disk provided that `(f z).re ≤ M` for all `|z| < R`.
After obtaining bounds on `w`, we invert the transformation to recover bounds on `f`.

## Tags

complex analysis, Borel, Carathéodory, analytic function, growth bound
-/

open Metric

namespace Complex

variable {f : Complex -> Complex} {s : Set Complex} {M R : Real} {z w : Complex}

section SchwarzTransform

/--
lemma `eq_mul_div_one_add_of_eq_div_sub` / 引理 `eq_mul_div_one_add_of_eq_div_sub`

English:
lemma eq_mul_div_one_add_of_eq_div_sub
  statement: (_ : M != 0) (_ : 2 * M - z != 0)
  proof: by
  rw [h]; field_simp; ring_nf; rw [mul_inv_cancel_right₀]; norm_cast

中文:
引理 eq_mul_div_one_add_of_eq_div_sub
  结论: (_ : M != 0) (_ : 2 * M - z != 0)
  证明: by
  rw [h]; field_simp; ring_nf; rw [mul_inv_cancel_right₀]; norm_cast

Depends on / 依赖: ring_nf
-/
lemma eq_mul_div_one_add_of_eq_div_sub (_ : M != 0) (_ : 2 * M - z != 0)
    (h : w = z / (2 * M - z)) : z = 2 * M * w / (1 + w) := by
  rw [h]; field_simp; ring_nf; rw [mul_inv_cancel_right₀]; norm_cast

/--
lemma `norm_two_mul_div_one_add_le` / 引理 `norm_two_mul_div_one_add_le`

English:
lemma norm_two_mul_div_one_add_le
  given: (hM : 0 < M) (hw : ‖w‖ < 1)
  proof: by
  simp only [norm_div, norm_mul, norm_ofNat, norm_real, Real.norm_eq_abs, abs_of_pos hM]
  gcongr
  rw [← norm_one (α := Complex)]; exact norm_sub_le_norm_add 1 w

中文:
引理 norm_two_mul_div_one_add_le
  条件: (hM : 0 < M) (hw : ‖w‖ < 1)
  证明: by
  simp only [norm_div, norm_mul, norm_ofNat, norm_real, Real.norm_eq_abs, abs_of_pos hM]
  gcongr
  rw [← norm_one (α := Complex)]; exact norm_sub_le_norm_add 1 w

Depends on / 依赖: Real.norm_eq_abs, abs_of_pos, norm_div, norm_eq_abs, norm_mul, norm_ofNat, norm_one, norm_real, norm_sub_le_norm_add
-/
lemma norm_two_mul_div_one_add_le (hM : 0 < M) (hw : ‖w‖ < 1) :
    ‖2 * ↑M * w / (1 + w)‖ <= 2 * M * ‖w‖ / (1 - ‖w‖) := by
  simp only [norm_div, norm_mul, norm_ofNat, norm_real, Real.norm_eq_abs, abs_of_pos hM]
  gcongr
  rw [← norm_one (α := Complex)]; exact norm_sub_le_norm_add 1 w

/--
lemma `norm_le_norm_two_mul_sub` / 引理 `norm_le_norm_two_mul_sub`

English:
lemma norm_le_norm_two_mul_sub
  given: (_ : 0 < M) (_ : z.re <= M)
  statement: ‖z‖ <= ‖2 * M - z‖
  proof: by
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  suffices z.re * z.re <= (2 * M - z.re) * (2 * M - z.re) by simpa [Complex.sq_norm, normSq_apply]
  nlinarith

中文:
引理 norm_le_norm_two_mul_sub
  条件: (_ : 0 < M) (_ : z.re <= M)
  结论: ‖z‖ <= ‖2 * M - z‖
  证明: by
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  suffices z.re * z.re <= (2 * M - z.re) * (2 * M - z.re) by simpa [Complex.sq_norm, normSq_apply]
  nlinarith

Depends on / 依赖: Complex.sq_norm, normSq_apply, sq_norm, z.re
-/
lemma norm_le_norm_two_mul_sub (_ : 0 < M) (_ : z.re <= M) : ‖z‖ <= ‖2 * M - z‖ := by
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  suffices z.re * z.re <= (2 * M - z.re) * (2 * M - z.re) by simpa [Complex.sq_norm, normSq_apply]
  nlinarith

/--
lemma `schwarz_applied` / 引理 `schwarz_applied`

English:
lemma schwarz_applied
  statement: (hM : 0 < M) (hf : DifferentiableOn Complex f (ball 0 R))
  proof: by
  rw [← dist_zero_right]; rw [← dist_zero_right]
  nth_rw 1 [← zero_div (2 * M - f 0), ← hf₂]
  apply dist_le_div_mul_dist_of_mapsTo_ball (R₂ := 1) ?_ (fun x hx => ?_) hz
  · apply hf.div (hf.const_sub _) fun x hx h => ?_
    have := sub_eq_zero.mp h ▸ hf₁ hx
    aesop
  · simpa [hf₂] using
     

中文:
引理 schwarz_applied
  结论: (hM : 0 < M) (hf : DifferentiableOn 复形 f (ball 0 R))
  证明: by
  rw [← dist_zero_right]; rw [← dist_zero_right]
  nth_rw 1 [← zero_div (2 * M - f 0), ← hf₂]
  apply dist_le_div_mul_dist_of_mapsTo_ball (R₂ := 1) ?_ (fun x hx => ?_) hz
  · apply hf.div (hf.const_sub _) fun x hx h => ?_
    have := sub_eq_zero.mp h ▸ hf₁ hx
    aesop
  · simpa [hf₂] using
     

Depends on / 依赖: const_sub, dist_le_div_mul_dist_of_mapsTo_ball, dist_zero_right, hf.const_sub, hf.div, norm_le_norm_two_mul_sub, nth_rw, sub_eq_zero, sub_eq_zero.mp, zero_div
-/
lemma schwarz_applied (hM : 0 < M) (hf : DifferentiableOn Complex f (ball 0 R))
    (hf₁ : Set.MapsTo f (ball 0 R) {z | z.re <= M}) (hz : z in ball 0 R) (hf₂ : f 0 = 0) :
    ‖f z / (2 * M - f z)‖ <= (1 / R) * ‖z‖ := by
  rw [← dist_zero_right]; rw [← dist_zero_right]
  nth_rw 1 [← zero_div (2 * M - f 0), ← hf₂]
  apply dist_le_div_mul_dist_of_mapsTo_ball (R₂ := 1) ?_ (fun x hx => ?_) hz
  · apply hf.div (hf.const_sub _) fun x hx h => ?_
    have := sub_eq_zero.mp h ▸ hf₁ hx
    aesop
  · simpa [hf₂] using
      div_le_one_of_le₀ (norm_le_norm_two_mul_sub hM (hf₁ hx)) (by positivity)

end SchwarzTransform

section BorelCaratheodory

/-- **Borel-Carathéodory theorem** for functions vanishing at the origin.

If `f` is analytic on the open ball `‖z‖ < R`, satisfies `(f z).re ≤ M` for all such `z`,
and `f 0 = 0`, then `‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖)` for all `‖z‖ < R`. -/
public theorem borelCaratheodory_zero (hM : 0 < M) (hf : DifferentiableOn Complex f (ball 0 R))
    (hf₁ : Set.MapsTo f (ball 0 R) {z | z.re <= M}) (hR : 0 < R) (hz : z in ball 0 R)
    (hf₂ : f 0 = 0) : ‖f z‖ <= 2 * M * ‖z‖ / (R - ‖z‖) := by
  set w := f z / (2 * M - f z)
  have hzR : ‖z‖ < R := mem_ball_zero_iff.mp hz
  have hwR := by simpa only [dist_zero_right, div_one, mul_comm (1 / R), mul_one_div]
    using schwarz_applied hM hf hf₁ hz hf₂
  have h_denom : 2 * M - f z != 0 := sub_ne_zero_of_ne (fun h => by simpa [← h, hM] using hf₁ hz)
  calc ‖f z‖
    _ = ‖2 * M * w / (1 + w)‖ := by rw [eq_mul_div_one_add_of_eq_div_sub hM.ne' h_denom rfl]
    _ <= 2 * M * ‖w‖ / (1 - ‖w‖) := by
      simp only [norm_div, norm_mul, norm_ofNat, norm_real, Real.norm_eq_abs, abs_of_pos hM]
      gcongr
      · linarith [hwR.trans_lt ((div_lt_one₀ hR).mpr hzR)]
      · simpa using norm_sub_le_norm_add 1 w
    _ = 2 * M * (‖w‖ / (1 - ‖w‖)) := by ring
    _ <= 2 * M * (‖z‖ / R / (1 - ‖z‖ / R)) := by gcongr; simpa [div_lt_one hR]
    _ = 2 * M * ‖z‖ / (R - ‖z‖) := by field_simp

/-- **Borel-Carathéodory theorem**.

If `f` is analytic on the open ball `‖z‖ < R` and satisfies `(f z).re ≤ M` for all such `z`,
then `‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖)` for all `‖z‖ < R`. -/
public theorem borelCaratheodory (hM : 0 < M) (hf : DifferentiableOn Complex f (ball 0 R))
    (hf₁ : Set.MapsTo f (ball 0 R) {z | z.re <= M}) (hR : 0 < R) (hz : z in ball 0 R) :
    ‖f z‖ <= 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) := by
  have hfz : ‖f z - f 0‖ <= 2 * (M + ‖f 0‖) * ‖z‖ / (R - ‖z‖) := by
    apply borelCaratheodory_zero (by positivity) (by fun_prop) ?_ hR hz (by simp)
    intro x hx
    simp only [Set.mem_ofPred_eq, sub_re]
    calc (f x).re - (f 0).re <= M - (f 0).re := by gcongr; exact hf₁ hx
      _ <= M + ‖f 0‖ := by linarith [neg_le_abs (f 0).re, abs_re_le_norm (f 0)]
  have h_denom_ne : R - ‖z‖ != 0 := by linarith [mem_ball_zero_iff.mp hz]
  calc ‖f z‖ <= ‖f z - f 0‖ + ‖f 0‖ := norm_le_norm_sub_add _ _
    _ <= 2 * (M + ‖f 0‖) * ‖z‖ / (R - ‖z‖) + ‖f 0‖ := by gcongr
    _ = 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) := by field_simp; ring

end BorelCaratheodory

end Complex
